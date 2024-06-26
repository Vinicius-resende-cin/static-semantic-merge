package gitManager;

import groovy.lang.Tuple2;
import project.MergeCommit;
import project.Project;
import services.dataCollectors.modifiedLinesCollector.*;
import util.FileManager;
import util.TypeNameHelper;

import java.util.*;

public class ModifiedLinesManager {
    ModifiedLinesCollector modifiedLinesCollector;
    FileManager fileManager;
    ModifiedMethodsHelper modifiedMethodsHelper;

    public ModifiedLinesManager (String dependenciesPath) {
        this.modifiedLinesCollector = new ModifiedLinesCollector(dependenciesPath);
        this.modifiedMethodsHelper = new ModifiedMethodsHelper("diffj.jar", dependenciesPath);
    }

    public List<CollectedMergeMethodData> collectData(Project project, MergeCommit mergeCommit) {
        List<CollectedMergeMethodData> collectedMergeMethodDataList = new ArrayList<>();
       Set<String> mutuallyModifiedFiles = this.modifiedLinesCollector.getFilesModifiedByBothParents(project, mergeCommit);

        for (String filePath : mutuallyModifiedFiles) {
            Set<ModifiedMethod> allModifiedMethods = this.modifiedMethodsHelper.getModifiedMethods(project, filePath, mergeCommit.getAncestorSHA(), mergeCommit.getSHA());
            Map<String, Tuple2<ModifiedMethod, ModifiedMethod>> mutuallyModifiedMethods = this.modifiedLinesCollector.getMutuallyModifiedMethods(project, mergeCommit, filePath);

            boolean fileHasMutuallyModifiedMethods = !mutuallyModifiedMethods.isEmpty();
            if (fileHasMutuallyModifiedMethods) {
                String className = TypeNameHelper.getFullyQualifiedName(project, filePath, mergeCommit.getAncestorSHA());

                for (ModifiedMethod method : allModifiedMethods) {
                    Tuple2<ModifiedMethod, ModifiedMethod> leftAndRightMethods = mutuallyModifiedMethods.get(method.getSignature());

                    boolean methodWasModifiedByBothParents = leftAndRightMethods != null;
                    if (methodWasModifiedByBothParents) {
                        collectedMergeMethodDataList.add(this.collectMethodData(leftAndRightMethods, method, project, mergeCommit, className));
                    }

                }

            }
        }

        System.out.println(project.getName() + " - ModifiedLinesCollector collection finished");
        return collectedMergeMethodDataList;
    }

    private CollectedMergeMethodData collectMethodData(Tuple2<ModifiedMethod, ModifiedMethod> leftAndRightMethods, ModifiedMethod mergeMethod, Project project, MergeCommit mergeCommit, String className) {
        ModifiedMethod leftMethod = leftAndRightMethods.getV1();
        ModifiedMethod rightMethod = leftAndRightMethods.getV2();

        Set<Integer> leftAddedLines = new HashSet<Integer>();
        Set<Integer> leftDeletedLines = new HashSet<Integer>();
        Set<Integer> rightAddedLines = new HashSet<Integer>();
        Set<Integer> rightDeletedLines = new HashSet<Integer>();

        for (ModifiedLine mergeLine : mergeMethod.getModifiedLines()) {
            if (leftMethod.getModifiedLines().contains(mergeLine)) {
                if (mergeLine.getType() == ModifiedLine.ModificationType.Removed) {
                    leftDeletedLines.add(mergeLine.getNumber());
                } else {
                    leftAddedLines.add(mergeLine.getNumber());
                }
            }

            if (rightMethod.getModifiedLines().contains(mergeLine)) {
                if (mergeLine.getType() == ModifiedLine.ModificationType.Removed) {
                    rightDeletedLines.add(mergeLine.getNumber());
                } else {
                    rightAddedLines.add(mergeLine.getNumber());
                }
            }
        }

        CollectedMergeMethodData collectedMergeMethodData = new CollectedMergeMethodData(project, mergeCommit, className, mergeMethod.getSignature(), leftAddedLines, leftDeletedLines, rightAddedLines, rightDeletedLines);
        System.out.println(collectedMergeMethodData.toString());

        return collectedMergeMethodData;
    }
}
