package main;

import buildManager.BuildGenerator;
import csvManager.CsvManager;
import entrypointManager.EntrypointManager;
import gitManager.CollectedMergeMethodData;
import gitManager.CommitManager;
import gitManager.MergeManager;
import gitManager.ModifiedLinesManager;
import org.apache.commons.io.FileUtils;
import project.MergeCommit;
import project.Project;
import services.dataCollectors.modifiedLinesCollector.ModifiedMethod;
import services.outputProcessors.GenerateSootInputFilesOutputProcessor;
import services.outputProcessors.soot.RunSootAnalysisOutputProcessor;

import java.io.*;
import java.util.*;


public class StaticAnalysisMerge {

    private final Arguments args;

    StaticAnalysisMerge(Arguments args){
        this.args = args;
    }

    public void run() {
        //DependenciesManager dependenciesManager = new DependenciesManager();
        MergeManager mergeManager = new MergeManager();
        BuildGenerator buildGenerator = new BuildGenerator(this.args.getGradlePath(), this.args.getMavenPath(), this.args.getTargetProjectRoot());
        CommitManager commitManager = new CommitManager(this.args.getHead(), this.args.getParents(), this.args.getBase());
        Project project = new Project("project", this.args.getTargetProjectRoot());
        ModifiedLinesManager modifiedLinesManager = new ModifiedLinesManager(this.args.getSsmDependenciesPath());
        EntrypointManager entrypointManager = new EntrypointManager(this.args.getSsmDependenciesPath(), this.args.getClassName(), this.args.getMainMethod());

        try {
            //dependenciesManager.copyAuxFilesToProject(this.args.getSsmPath());

            MergeCommit mergeCommit = commitManager.buildMergeCommit();

            Process buildGeneration = buildGenerator.generateBuild();
            buildGeneration.waitFor();

            if(buildGeneration.exitValue() != 0) {
                System.out.println("Could not generate a valid build");
                mergeManager.revertCommit(mergeCommit.getLeftSHA());
                return;
            }

            File buildJar = buildGenerator.getBuildJar();

            File dest = new File("files/project/" + mergeCommit.getSHA() + "/original-without-dependencies/merge/build.jar");
            FileUtils.copyFile(buildJar, dest);

            List<ModifiedMethod> entrypoints = new ArrayList<>();
            if (this.args.getEntrypoints() != null && this.args.getEntrypoints().length > 0) {
                for (String entrypoint : this.args.getEntrypoints()) {
                    entrypoints.add(new ModifiedMethod(entrypoint));
                }
            } else {
                entrypointManager.configureSoot(dest.getPath(), this.args.getClassName());
                entrypoints = entrypointManager.run(project, mergeCommit);
            }

            List<CollectedMergeMethodData> collectedMergeMethodDataList = modifiedLinesManager.collectData(project, mergeCommit);
            CsvManager csvManager = new CsvManager();
            csvManager.transformCollectedDataIntoCsv(collectedMergeMethodDataList, entrypoints, ".");
            csvManager.trimSpacesAndSpecialChars(new File("data/results-with-build-information.csv"));


            GenerateSootInputFilesOutputProcessor generateSootInputFilesOutputProcessor = new GenerateSootInputFilesOutputProcessor(this.args.getScriptsPath());
            generateSootInputFilesOutputProcessor.convertToSootScript(".");

            Map<String, Set<Integer>[]> modifications = new HashMap<>();
            for(CollectedMergeMethodData data : collectedMergeMethodDataList) {
                String path = "files/"+ data.getProject().getName() + "/" + mergeCommit.getSHA() + "/changed-methods/" + data.getClassName() +"/" + data.getMethodSignature();
                path = path.replaceAll(" ", "");
                path = path.replaceAll("[+^?<>|]*", "");
                File left = new File( path + "/left-right-lines.csv");
                File right = new File(path + "/right-left-lines.csv");

                csvManager.trimBlankLines(left);
                csvManager.trimBlankLines(right);

                if (!modifications.containsKey(data.getClassName())) {
                    Set<Integer>[] classModifications = new Set[4];
                    classModifications[0] = data.getLeftAddedLines();
                    classModifications[1] = data.getLeftDeletedLines();
                    classModifications[2] = data.getRightAddedLines();
                    classModifications[3] = data.getRightDeletedLines();

                    modifications.put(data.getClassName(), classModifications);
                } else {
                    Set<Integer>[] classModifications = modifications.get(data.getClassName());
                    classModifications[0].addAll(data.getLeftAddedLines());
                    classModifications[1].addAll(data.getLeftDeletedLines());
                    classModifications[2].addAll(data.getRightAddedLines());
                    classModifications[3].addAll(data.getRightDeletedLines());
                }
            }

            // Exporting the modified lines
            for(CollectedMergeMethodData data : collectedMergeMethodDataList) {
                String path = "files/" + data.getProject().getName() + "/" + mergeCommit.getSHA() + "/changed-methods/" + data.getClassName() + "/" + data.getMethodSignature();
                path = path.replaceAll(" ", "");
                path = path.replaceAll("[+^?<>|]*", "");

                FileWriter fw = new FileWriter(path + "/modified-lines.txt");
                for (String className : modifications.keySet()) {
                    Set<Integer>[] classModifications = modifications.get(className);
                    try {
                        fw.write("Class: " + className + "\n");
                        fw.write("Left added lines: " + classModifications[0].toString() + "\n");
                        fw.write("Left deleted lines: " + classModifications[1].toString() + "\n");
                        fw.write("Right added lines: " + classModifications[2].toString() + "\n");
                        fw.write("Right deleted lines: " + classModifications[3].toString() + "\n\n");
                    } catch (Exception e) {
                        System.out.println("error exporting the modified lines for project " + data.getProject().getName() + " " + e.getMessage());
                    }
                }
                fw.close();
            }

            RunSootAnalysisOutputProcessor runSootAnalysisOutputProcessor = new RunSootAnalysisOutputProcessor(this.args.getSsmDependenciesPath());
            runSootAnalysisOutputProcessor.executeAnalyses(".");

            File results = new File("./data/soot-results.csv");

            if(csvManager.hasConflict(results)){
               // mergeManager.revertCommit(mergeCommit.getLeftSHA());
            }

            //dependenciesManager.deleteAuxFiles(this.args.getSsmPath());

        } catch (IOException | InterruptedException /*| InterruptedException e*/e) {
            e.printStackTrace();
        }
    }
}
