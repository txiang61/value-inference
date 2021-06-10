package value;

import checkers.inference.InferenceAnnotatedTypeFactory;
import checkers.inference.InferenceMain;
import checkers.inference.VariableAnnotator;
import checkers.inference.dataflow.InferenceAnalysis;
import checkers.inference.dataflow.InferenceTransfer;
import checkers.inference.model.AnnotationLocation;
import checkers.inference.model.ComparisonVariableSlot;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.ConstraintManager;
import checkers.inference.model.RefinementVariableSlot;
import checkers.inference.model.Slot;
import checkers.inference.qual.VarAnnot;
import com.sun.source.tree.Tree;
import java.util.Set;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.dataflow.analysis.ConditionalTransferResult;
import org.checkerframework.dataflow.analysis.FlowExpressions;
import org.checkerframework.dataflow.analysis.FlowExpressions.Receiver;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.AssignmentNode;
import org.checkerframework.dataflow.cfg.node.EqualToNode;
import org.checkerframework.dataflow.cfg.node.FieldAccessNode;
import org.checkerframework.dataflow.cfg.node.GreaterThanNode;
import org.checkerframework.dataflow.cfg.node.GreaterThanOrEqualNode;
import org.checkerframework.dataflow.cfg.node.LessThanNode;
import org.checkerframework.dataflow.cfg.node.LessThanOrEqualNode;
import org.checkerframework.dataflow.cfg.node.LocalVariableNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.NotEqualNode;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.AnnotationUtils;

public class ValueInferenceTransfer extends InferenceTransfer {

    private ValueInferenceAnnotatedTypeFactory typeFactory;

    public ValueInferenceTransfer(InferenceAnalysis analysis) {
        super(analysis);
        typeFactory = (ValueInferenceAnnotatedTypeFactory) analysis.getTypeFactory();
    }

    private InferenceAnalysis getInferenceAnalysis() {
        return (InferenceAnalysis) analysis;
    }

    private void createComparisonVariableSlot(Node node, CFStore thenStore, CFStore elseStore) {
        // Only create refinement comparison slot for variables
        Node var = node;
        if (node instanceof AssignmentNode) {
            AssignmentNode a = (AssignmentNode) node;
            var = a.getTarget();
        }
        if (!(var instanceof LocalVariableNode) && !(var instanceof FieldAccessNode)) {
            return;
        }
        Tree tree = var.getTree();
        ConstraintManager constraintManager = InferenceMain.getInstance().getConstraintManager();
        AnnotatedTypeMirror atm = typeFactory.getAnnotatedType(tree);
        Slot slotToRefine = getInferenceAnalysis().getSlotManager().getSlot(atm);
        // TODO: Understand why there are null slots
        if (slotToRefine == null) {
            return;
        }
        if (slotToRefine instanceof ConstantSlot) {
            return;
        }
        while (slotToRefine instanceof RefinementVariableSlot) {
            slotToRefine = ((RefinementVariableSlot) slotToRefine).getRefined();
        }

        AnnotationLocation location =
                VariableAnnotator.treeToLocation(analysis.getTypeFactory(), tree);
        // TODO: find out why there are missing location
        if (location == AnnotationLocation.MISSING_LOCATION) {
            return;
        }
        ComparisonVariableSlot thenSlot =
                getInferenceAnalysis()
                        .getSlotManager()
                        .createComparisonVariableSlot(location, slotToRefine, true);
        constraintManager.addSubtypeConstraint(thenSlot, slotToRefine);
        ComparisonVariableSlot elseSlot =
                getInferenceAnalysis()
                        .getSlotManager()
                        .createComparisonVariableSlot(location, slotToRefine, false);
        constraintManager.addSubtypeConstraint(elseSlot, slotToRefine);
        AnnotationMirror thenAm = getInferenceAnalysis().getSlotManager().getAnnotation(thenSlot);
        AnnotationMirror elseAm = getInferenceAnalysis().getSlotManager().getAnnotation(elseSlot);

        // If node is assignment, iterate over lhs; otherwise, just node.
        Receiver rec;
        rec = FlowExpressions.internalReprOf(getInferenceAnalysis().getTypeFactory(), var);
        thenStore.clearValue(rec);
        thenStore.insertValue(rec, thenAm);
        elseStore.clearValue(rec);
        elseStore.insertValue(rec, elseAm);
    }

    @Override
    public TransferResult<CFValue, CFStore> visitEqualTo(
            EqualToNode n, TransferInput<CFValue, CFStore> in) {
        TransferResult<CFValue, CFStore> result = super.visitEqualTo(n, in);
        CFStore thenStore = result.getThenStore();
        CFStore elseStore = result.getElseStore();

        createComparisonVariableSlot(n.getLeftOperand(), thenStore, elseStore);
        createComparisonVariableSlot(n.getRightOperand(), thenStore, elseStore);

        CFValue newResultValue =
                getInferenceAnalysis()
                        .createAbstractValue(typeFactory.getAnnotatedType(n.getTree()));
        return new ConditionalTransferResult<>(newResultValue, thenStore, elseStore);
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNotEqual(
            NotEqualNode n, TransferInput<CFValue, CFStore> in) {
        TransferResult<CFValue, CFStore> result = super.visitNotEqual(n, in);
        CFStore thenStore = result.getThenStore();
        CFStore elseStore = result.getElseStore();

        createComparisonVariableSlot(n.getLeftOperand(), thenStore, elseStore);
        createComparisonVariableSlot(n.getRightOperand(), thenStore, elseStore);

        CFValue newResultValue =
                analysis.createAbstractValue(typeFactory.getAnnotatedType(n.getTree()));
        return new ConditionalTransferResult<>(newResultValue, thenStore, elseStore);
    }

    @Override
    public TransferResult<CFValue, CFStore> visitGreaterThan(
            GreaterThanNode n, TransferInput<CFValue, CFStore> in) {
        TransferResult<CFValue, CFStore> result = super.visitGreaterThan(n, in);
        CFStore thenStore = result.getThenStore();
        CFStore elseStore = result.getElseStore();

        createComparisonVariableSlot(n.getLeftOperand(), thenStore, elseStore);
        createComparisonVariableSlot(n.getRightOperand(), thenStore, elseStore);

        CFValue newResultValue =
                analysis.createAbstractValue(typeFactory.getAnnotatedType(n.getTree()));
        return new ConditionalTransferResult<>(newResultValue, thenStore, elseStore);
    }

    @Override
    public TransferResult<CFValue, CFStore> visitGreaterThanOrEqual(
            GreaterThanOrEqualNode n, TransferInput<CFValue, CFStore> in) {
        TransferResult<CFValue, CFStore> result = super.visitGreaterThanOrEqual(n, in);
        CFStore thenStore = result.getThenStore();
        CFStore elseStore = result.getElseStore();

        createComparisonVariableSlot(n.getLeftOperand(), thenStore, elseStore);
        createComparisonVariableSlot(n.getRightOperand(), thenStore, elseStore);

        CFValue newResultValue =
                analysis.createAbstractValue(typeFactory.getAnnotatedType(n.getTree()));
        return new ConditionalTransferResult<>(newResultValue, thenStore, elseStore);
    }

    @Override
    public TransferResult<CFValue, CFStore> visitLessThan(
            LessThanNode n, TransferInput<CFValue, CFStore> in) {
        TransferResult<CFValue, CFStore> result = super.visitLessThan(n, in);
        CFStore thenStore = result.getThenStore();
        CFStore elseStore = result.getElseStore();

        createComparisonVariableSlot(n.getLeftOperand(), thenStore, elseStore);
        createComparisonVariableSlot(n.getRightOperand(), thenStore, elseStore);

        CFValue newResultValue =
                analysis.createAbstractValue(typeFactory.getAnnotatedType(n.getTree()));
        return new ConditionalTransferResult<>(newResultValue, thenStore, elseStore);
    }

    @Override
    public TransferResult<CFValue, CFStore> visitLessThanOrEqual(
            LessThanOrEqualNode n, TransferInput<CFValue, CFStore> in) {
        TransferResult<CFValue, CFStore> result = super.visitLessThanOrEqual(n, in);
        CFStore thenStore = result.getThenStore();
        CFStore elseStore = result.getElseStore();

        createComparisonVariableSlot(n.getLeftOperand(), thenStore, elseStore);
        createComparisonVariableSlot(n.getRightOperand(), thenStore, elseStore);

        CFValue newResultValue =
                analysis.createAbstractValue(typeFactory.getAnnotatedType(n.getTree()));
        return new ConditionalTransferResult<>(newResultValue, thenStore, elseStore);
    }

    @Override
    public TransferResult<CFValue, CFStore> visitLocalVariable(
            LocalVariableNode n, TransferInput<CFValue, CFStore> in) {
        TransferResult<CFValue, CFStore> result = super.visitLocalVariable(n, in);
        CFStore store = result.getRegularStore();
        Receiver rec = FlowExpressions.internalReprOf(getInferenceAnalysis().getTypeFactory(), n);

        CFValue value = store.getValue(rec);
        if (value == null) {
            return result;
        }

        Set<AnnotationMirror> ams = value.getAnnotations();

        for (AnnotationMirror am : ams) {
            if (AnnotationUtils.areSameByClass(am, VarAnnot.class)) {
                InferenceAnnotatedTypeFactory typeFactory =
                        (InferenceAnnotatedTypeFactory) analysis.getTypeFactory();
                AnnotatedTypeMirror atm = typeFactory.getAnnotatedType(n.getTree());
                atm.replaceAnnotation(am);

                // add refinement variable value to output
                CFValue newValue = analysis.createAbstractValue(atm);

                // This is a bit of a hack, but we want the LHS to now get the refinement
                // annotation.
                // So change the value for LHS that is already in the store.
                getInferenceAnalysis().getNodeValues().put(n, newValue);

                store.updateForAssignment(n, newValue);
                return new RegularTransferResult<CFValue, CFStore>(
                        finishValue(newValue, store), store);
            }
        }

        return result;
    }
}
