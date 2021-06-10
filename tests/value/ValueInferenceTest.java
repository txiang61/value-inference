package value;

import checkers.inference.test.CFInferenceTest;
import java.io.File;
import java.util.ArrayList;
import java.util.List;
import org.checkerframework.framework.test.TestUtilities;
import org.checkerframework.javacutil.Pair;
import org.junit.runners.Parameterized.Parameters;
import value.solver.ValueSolverEngine;

public class ValueInferenceTest extends CFInferenceTest {

    public ValueInferenceTest(File testFile) {
        super(
                testFile,
                value.ValueChecker.class,
                "value",
                "-Anomsgtext",
                "-d",
                "tests/build/outputdir");
    }

    @Override
    public boolean useHacks() {
        return true;
    }

    @Override
    public Pair<String, List<String>> getSolverNameAndOptions() {
        final String solverName = ValueSolverEngine.class.getCanonicalName();
        List<String> solverOptions = new ArrayList<>();
        solverOptions.add("optimizingMode=true");
        return Pair.<String, List<String>>of(solverName, solverOptions);
    }

    @Parameters
    public static List<File> getTestFiles() {
        return new ArrayList<>(
            TestUtilities.getJavaFilesAsArgumentList(new File("testing")));
    }
}
