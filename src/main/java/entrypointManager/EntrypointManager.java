package entrypointManager;

import org.jgrapht.Graph;
import org.jgrapht.alg.interfaces.LowestCommonAncestorAlgorithm;
import org.jgrapht.alg.lca.NaiveLCAFinder;
import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.graph.DefaultEdge;
import project.MergeCommit;
import project.Project;
import services.dataCollectors.modifiedLinesCollector.ModifiedLinesCollector;
import services.dataCollectors.modifiedLinesCollector.ModifiedMethod;
import services.dataCollectors.modifiedLinesCollector.ModifiedMethodsHelper;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;

import java.util.*;
import java.util.stream.Collectors;

public class EntrypointManager {

    ModifiedLinesCollector modifiedLinesCollector;

    ModifiedMethodsHelper modifiedMethodsHelper;

    String mainClassName;

    String mainMethodName;

    public EntrypointManager (String dependenciesPath, String mainClassName, String mainMethodName) {
        this.mainClassName = mainClassName;
        this.mainMethodName = mainMethodName;
        this.modifiedLinesCollector = new ModifiedLinesCollector(dependenciesPath);
        this.modifiedMethodsHelper = new ModifiedMethodsHelper("diffj.jar", dependenciesPath);
    }

    public List<ModifiedMethod> run(Project project,  MergeCommit mergeCommit){
        Set<String> allModifiedFiles = this.modifiedLinesCollector.getAllModifiedFiles(project, mergeCommit);

        Set<ModifiedMethod> left = new HashSet<>();
        Set<ModifiedMethod> right = new HashSet<>();
        for (String filePath : allModifiedFiles) {
             left.addAll(this.modifiedMethodsHelper.getAllModifiedMethods(project, filePath, mergeCommit.getAncestorSHA(), mergeCommit.getLeftSHA()));
             right.addAll(this.modifiedMethodsHelper.getAllModifiedMethods(project, filePath,  mergeCommit.getAncestorSHA(), mergeCommit.getRightSHA()));
        }

       return findCommonAncestor(left, right);
    }

    public void configureSoot(String classpath, String classes) {
        // Configurar as opções do Soot
        String[] sootArgs = {
                "-cp", classpath,
                "-pp",
                "-f", "J",
                "-w",
                "--allow-phantom-refs",
                "-p", "jb", "use-original-names:true",
                "-p", "cg.spark", "enabled:true",
                classes
        };

        soot.Main.main(sootArgs);
        Scene.v().loadNecessaryClasses();

    }

    public Iterator<Edge> getCallGraphFromMain(String className, String methodName){

        SootClass sootClass = Scene.v().loadClassAndSupport(className);
        SootMethod mainMethod;
        try {
            mainMethod = sootClass.getMethodByName(methodName);
        } catch (RuntimeException e) {
            mainMethod = sootClass.getMethodByName("main");
        }

        CallGraph callGraph = Scene.v().getCallGraph();

        return callGraph.edgesOutOf(mainMethod);
    }

    /**
     * Método para aplicar o algoritmo de busca do ancestral comum mais recente entre as alterações de left e right.

     * Se left e right estiverem vazios, lançar uma exceção.
     * Se left e right tiverem apenas um elemento, buscar o ancestral comum mais recente apenas desse par.
     * Se left ou right tiverem mais de um elemento, buscar o ancestral comum mais recente para todas as combinações de pares.
     * Se nenhum acestral for encontrado, retonra uma exceção.

     * @param leftChanges   Conjunto de métodos modificados no lado esquerdo.
     * @param rightChanges  Conjunto de métodos modificados no lado direito.
     * @return O ancestral comum mais recente ou null se nenhum for encontrado.
     * @throws IllegalArgumentException Se leftChanges ou rightChanges estiverem vazios.
     * @throws RuntimeException         Se nenhum ancestral comum for encontrado.
     */

    public List<ModifiedMethod> findCommonAncestor(Set<ModifiedMethod> leftChanges, Set<ModifiedMethod> rightChanges) {
        DefaultDirectedGraph<ModifiedMethod, DefaultEdge> graph = createDirectedGraph();

        if (leftChanges.isEmpty() || rightChanges.isEmpty()) {
            throw new IllegalArgumentException("leftChanges and rightChanges cannot be empty");
        }

        List<ModifiedMethod> commonAncestors = new ArrayList<>();

        for (ModifiedMethod leftMethod : leftChanges) {
            for (ModifiedMethod rightMethod : rightChanges) {
                ModifiedMethod ancestorsForPair = findCommonAncestorForPair(graph, leftMethod, rightMethod);
                if(ancestorsForPair != null){
                    commonAncestors.add(ancestorsForPair);
                }
            }
        }

        if (commonAncestors.isEmpty()) {
            throw new RuntimeException("No common ancestor found.");
        }

        return commonAncestors;
    }

    /**
     * Método para encontrar o ancestral comum mais recente para um par de modificações.
     *
     * @param graph        O grafo de chamadas.
     * @param leftMethod   Método modificado do lado esquerdo do par.
     * @param rightMethod  Método modificado do lado direito do par.
     * @return O ancestral comum mais recente ou null se nenhum for encontrado.
     */

    public ModifiedMethod findCommonAncestorForPair(DefaultDirectedGraph<ModifiedMethod, DefaultEdge> graph, ModifiedMethod leftMethod, ModifiedMethod rightMethod) {


        LowestCommonAncestorAlgorithm<ModifiedMethod> lcaAlgorithm = new NaiveLCAFinder<>(graph);

       if(graph.containsVertex(leftMethod) && graph.containsVertex(rightMethod)){
           return lcaAlgorithm.getLCA(leftMethod, rightMethod);
        }

        return null;
    }

    /**
     * Método para simplificar a assinatura de um método, removendo o pacote de cada parâmetro e mantendo o nome simplificado da classe.
     * @param signature Assinatura do método
     * @return A assinatura simplificada.
     */
    private String simplifyMethodSignature(String signature) {
        String args = signature.substring(signature.indexOf("(") + 1, signature.indexOf(")"));
        if (args.equals("")) {
            return signature;
        }

        String[] params = args.split(",");
        String simplifiedParams = Arrays.stream(params)
                .map(param -> {
                    String[] parts = param.split("\\.");
                    return parts[parts.length - 1];
                })
                .collect(Collectors.joining(", "));
        return signature.substring(0, signature.indexOf("(")) + "(" + simplifiedParams + ")>";
    }

    /**
     * Método recursivo para percorrer as arestas do CallGraph até uma profundidade determinada e convertê-las num DirectedGraph.
     * @param graph     O DirectedGraph a ser preenchido.
     * @param callGraph O CallGraph do Soot.
     * @param edges     As arestas a serem percorridas.
     * @param limit     O limite de profundidade da recursão.
     */
    private void traverseEdgeUntil(DefaultDirectedGraph<ModifiedMethod, DefaultEdge> graph, CallGraph callGraph, Iterator<Edge> edges, int limit) {
        if (!edges.hasNext() || limit == 0) {
            return;
        }

        while (edges.hasNext()) {
            Edge edge = edges.next();
            System.out.println(edge.getSrc() + " -> " + edge.getTgt());

            SootMethod src = (SootMethod) edge.getSrc();
            SootMethod tgt = (SootMethod) edge.getTgt();

            String srcSignature = simplifyMethodSignature(src.getSignature());
            String tgtSignature = simplifyMethodSignature(tgt.getSignature());
            ModifiedMethod sctModifiedMethod = new ModifiedMethod(srcSignature);
            ModifiedMethod tgtModifiedMethod = new ModifiedMethod(tgtSignature);

            graph.addVertex(sctModifiedMethod);
            graph.addVertex(tgtModifiedMethod);
            graph.addEdge(sctModifiedMethod, tgtModifiedMethod);

            this.traverseEdgeUntil(graph, callGraph, callGraph.edgesOutOf(edge.getTgt()), limit - 1);
        }
    }

    /**
     * Método para criar um grafo direcionado a partir do CallGraph do Soot.
     * @return O grafo direcionado.
     */
    public DefaultDirectedGraph<ModifiedMethod, DefaultEdge> createDirectedGraph() {
        // Criar o grafo direcionado
        CallGraph callGraph = Scene.v().getCallGraph();
        DefaultDirectedGraph<ModifiedMethod, DefaultEdge> graph = new DefaultDirectedGraph<>(DefaultEdge.class);

        // Adicionar os métodos e as arestas ao grafo
        Iterator<Edge> edges = getCallGraphFromMain(this.mainClassName, this.mainMethodName);
        traverseEdgeUntil(graph, callGraph, edges, 5);

        convertToDotGraph(graph);

        return graph;
    }

    private static void convertToDotGraph(Graph<ModifiedMethod, DefaultEdge> graph) {
        StringBuilder dot = new StringBuilder();
        dot.append("digraph {\n");

        // Adicionar vértices
        for (ModifiedMethod vertex : graph.vertexSet()) {
            dot.append("\t").append(vertex.getSignature()).append(";\n");
        }

        // Adicionar arestas
        for (DefaultEdge  edge : graph.edgeSet()) {
            ModifiedMethod source = graph.getEdgeSource(edge);
            ModifiedMethod target = graph.getEdgeTarget(edge);
            dot.append("\t").append(source.getSignature()).append(" -> ").append(target.getSignature()).append(";\n");
        }

        dot.append("}");

        System.out.println(dot);
    }

    private static boolean isMainMethod(SootMethod method) {
        return method.getName().equals("main");
    }
}