package gitManager;

import java.io.File;
import java.io.IOException;

public class DiffManager {
    File repoDir;
    File outputDir;

    public DiffManager(String repoPath, String outputPath) {
        this.repoDir = new File(repoPath);
        this.outputDir = new File(outputPath);
    }

    /**
     * Calculates the git diff between two commits and exports it to a file in the output directory.
     * @param commit1
     * @param commit2
     */
    public void exportDiff(String commit1, String commit2) {
        ProcessBuilder pb = new ProcessBuilder("git", "diff", commit1, commit2, "-U10000");
        pb.directory(this.repoDir);
        pb.redirectOutput(this.outputDir);
        pb.redirectError(ProcessBuilder.Redirect.INHERIT);

        try {
            Process p = pb.start();
            int exitCode = p.waitFor();
            if (exitCode == 0) {
                System.out.println("Diff exported successfully to " + this.outputDir.getAbsolutePath());
            } else {
                System.out.println("Diff exported failed to " + this.outputDir.getAbsolutePath());
            }
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
        }
    }
}
