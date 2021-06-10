package value;

import checkers.inference.InferenceAnnotatedTypeFactory;
import checkers.inference.InferenceChecker;
import checkers.inference.InferenceMain;
import checkers.inference.InferenceVisitor;
import checkers.inference.SlotManager;
import checkers.inference.VariableAnnotator;
import checkers.inference.model.ArithmeticConstraint.ArithmeticOperationKind;
import checkers.inference.model.ArithmeticVariableSlot;
import checkers.inference.model.ComparisonConstraint.ComparisonOperationKind;
import checkers.inference.model.ComparisonVariableSlot;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.ConstraintManager;
import checkers.inference.model.RefinementVariableSlot;
import checkers.inference.model.Slot;
import com.sun.source.tree.AssignmentTree;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.CompoundAssignmentTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.Tree.Kind;
import com.sun.source.tree.TypeCastTree;
import com.sun.source.tree.UnaryTree;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.TreeUtils;
import value.qual.IntRange;
import value.qual.UnknownVal;

public class ValueVisitor extends InferenceVisitor<ValueChecker, BaseAnnotatedTypeFactory> {

    /** The top type for this hierarchy. */
    protected final AnnotationMirror UNKNOWNVAL =
            AnnotationBuilder.fromClass(elements, UnknownVal.class);

    public ValueVisitor(
            ValueChecker checker,
            InferenceChecker ichecker,
            BaseAnnotatedTypeFactory factory,
            boolean infer) {
        super(checker, ichecker, factory, infer);
    }

    //    @Override
    //    public Void visitBinary(BinaryTree binaryTree, Void p) {
    //    	System.out.println(binaryTree);
    //
    //        // infer mode, adds constraints for binary operations
    //        if (infer) {
    //            SlotManager slotManager = InferenceMain.getInstance().getSlotManager();
    //            ConstraintManager constraintManager =
    //                    InferenceMain.getInstance().getConstraintManager();
    //
    //            InferenceAnnotatedTypeFactory iatf = (InferenceAnnotatedTypeFactory) atypeFactory;
    //
    //            AnnotatedTypeMirror lhsATM = iatf.getAnnotatedType(binaryTree.getLeftOperand());
    //            AnnotatedTypeMirror rhsATM = iatf.getAnnotatedType(binaryTree.getRightOperand());
    //            AnnotationMirror lhsAM =
    // lhsATM.getEffectiveAnnotationInHierarchy(iatf.getVarAnnot());
    //            AnnotationMirror rhsAM =
    // rhsATM.getEffectiveAnnotationInHierarchy(iatf.getVarAnnot());
    //            AnnotationMirror lhsAMVal = lhsATM.getEffectiveAnnotationInHierarchy(UNKNOWNVAL);
    //            AnnotationMirror rhsAMVal = rhsATM.getEffectiveAnnotationInHierarchy(UNKNOWNVAL);
    //            Slot lhs = slotManager.getSlot(lhsAM);
    //            Slot rhs = slotManager.getSlot(rhsAM);
    //
    //            Kind kind = binaryTree.getKind();
    //            switch (kind) {
    //                case PLUS:
    //                    if (TreeUtils.isStringConcatenation(binaryTree)) {
    //                        break;
    //                    }
    //                case MINUS:
    //                case MULTIPLY:
    //                case DIVIDE:
    //                case REMAINDER:
    //                case LEFT_SHIFT:
    //                case RIGHT_SHIFT:
    //                case UNSIGNED_RIGHT_SHIFT:
    //                case AND:
    //                case OR:
    //                case XOR:
    //                    if (lhsAMVal == null || rhsAMVal == null) {
    //                        ArithmeticOperationKind opKindplus =
    //                                ArithmeticOperationKind.fromTreeKind(kind);
    //                        ArithmeticVariableSlot avsResplus =
    //                                slotManager.getArithmeticVariableSlot(
    //                                        VariableAnnotator.treeToLocation(atypeFactory,
    // binaryTree));
    //                        constraintManager.addArithmeticConstraint(opKindplus, lhs, rhs,
    // avsResplus);
    //                        break;
    //                    }
    //                    if (AnnotationUtils.areSameByClass(lhsAMVal, IntRange.class)
    //                            && AnnotationUtils.areSameByClass(rhsAMVal, IntRange.class)) {
    //                    } else {
    //                        Slot lubSlot =
    //                                slotManager.getVariableSlot(
    //                                        atypeFactory.getAnnotatedType(binaryTree));
    //                        // Create LUB constraint by default
    //                        constraintManager.addSubtypeConstraint(lhs, lubSlot);
    //                        constraintManager.addSubtypeConstraint(rhs, lubSlot);
    //                    }
    //                    break;
    //                case EQUAL_TO: // ==
    //                case NOT_EQUAL_TO: // !=
    //                case GREATER_THAN: // >
    //                case GREATER_THAN_EQUAL: // >=
    //                case LESS_THAN: // <
    //                case LESS_THAN_EQUAL:
    //                    if (lhsAMVal == null || rhsAMVal == null) {
    ////                    	ComparableOperationKind opKindplus =
    ////                    			ComparableOperationKind.fromTreeKind(kind);
    ////                        constraintManager.addComparisonConstraint(opKindplus, lhs, rhs);
    //                        break;
    //                    }
    //                    if (AnnotationUtils.areSameByClass(lhsAMVal, IntRange.class)
    //                            && AnnotationUtils.areSameByClass(rhsAMVal, IntRange.class)) {
    //                    	break;
    //                    } // Create LUB constraint by default
    //                default:
    //                    Slot lubSlot =
    //
    // slotManager.getVariableSlot(atypeFactory.getAnnotatedType(binaryTree));
    //                    // Create LUB constraint by default
    //                    constraintManager.addSubtypeConstraint(lhs, lubSlot);
    //                    constraintManager.addSubtypeConstraint(rhs, lubSlot);
    //                    break;
    //            }
    //        }
    //
    //        return super.visitBinary(binaryTree, p);
    //    }

    @Override
    public Void visitBinary(BinaryTree binaryTree, Void p) {
        // infer mode, adds constraints for binary operations
        if (infer) {
            SlotManager slotManager = InferenceMain.getInstance().getSlotManager();
            ConstraintManager constraintManager =
                    InferenceMain.getInstance().getConstraintManager();

            InferenceAnnotatedTypeFactory iatf = (InferenceAnnotatedTypeFactory) atypeFactory;

            AnnotatedTypeMirror lhsATM = iatf.getAnnotatedType(binaryTree.getLeftOperand());
            AnnotatedTypeMirror rhsATM = iatf.getAnnotatedType(binaryTree.getRightOperand());
            AnnotationMirror lhsAM = lhsATM.getEffectiveAnnotationInHierarchy(iatf.getVarAnnot());
            AnnotationMirror rhsAM = rhsATM.getEffectiveAnnotationInHierarchy(iatf.getVarAnnot());
            if (lhsAM == null || rhsAM == null) {
                super.visitBinary(binaryTree, p);
            }
            Slot lhs = slotManager.getSlot(lhsAM);
            Slot rhs = slotManager.getSlot(rhsAM);

            Tree leftTree = binaryTree.getLeftOperand();
            if (leftTree instanceof AssignmentTree) {
                AssignmentTree t = (AssignmentTree) leftTree;
                leftTree = t.getVariable();
            }

            Kind kind = binaryTree.getKind();
            switch (kind) {
                case EQUAL_TO: // ==
                    if (leftTree instanceof IdentifierTree) {
                        ComparisonVariableSlot compThenRes =
                                slotManager.getComparisonVariableSlot(
                                        VariableAnnotator.treeToLocation(atypeFactory, leftTree),
                                        true);
                        constraintManager.addComparisonConstraint(
                                ComparisonOperationKind.EQUAL_TO, lhs, rhs, compThenRes);
                        ComparisonVariableSlot compElseRes =
                                slotManager.getComparisonVariableSlot(
                                        VariableAnnotator.treeToLocation(atypeFactory, leftTree),
                                        false);
                        constraintManager.addComparisonConstraint(
                                ComparisonOperationKind.NOT_EQUAL_TO, lhs, rhs, compElseRes);
                    }
                    break;
                case NOT_EQUAL_TO: // !=
                    if (leftTree instanceof IdentifierTree) {
                        ComparisonVariableSlot compThenRes =
                                slotManager.getComparisonVariableSlot(
                                        VariableAnnotator.treeToLocation(atypeFactory, leftTree),
                                        true);
                        constraintManager.addComparisonConstraint(
                                ComparisonOperationKind.NOT_EQUAL_TO, lhs, rhs, compThenRes);
                        ComparisonVariableSlot compElseRes =
                                slotManager.getComparisonVariableSlot(
                                        VariableAnnotator.treeToLocation(atypeFactory, leftTree),
                                        false);
                        constraintManager.addComparisonConstraint(
                                ComparisonOperationKind.EQUAL_TO, lhs, rhs, compElseRes);
                    }
                    break;
                case GREATER_THAN: // >
                    if (leftTree instanceof IdentifierTree) {
                        ComparisonVariableSlot compThenRes =
                                slotManager.getComparisonVariableSlot(
                                        VariableAnnotator.treeToLocation(atypeFactory, leftTree),
                                        true);
                        constraintManager.addComparisonConstraint(
                                ComparisonOperationKind.GREATER_THAN, lhs, rhs, compThenRes);
                        ComparisonVariableSlot compElseRes =
                                slotManager.getComparisonVariableSlot(
                                        VariableAnnotator.treeToLocation(atypeFactory, leftTree),
                                        false);
                        constraintManager.addComparisonConstraint(
                                ComparisonOperationKind.LESS_THAN_EQUAL, lhs, rhs, compElseRes);
                    }
                    break;
                case GREATER_THAN_EQUAL: // >=
                    if (leftTree instanceof IdentifierTree) {
                        ComparisonVariableSlot compThenRes =
                                slotManager.getComparisonVariableSlot(
                                        VariableAnnotator.treeToLocation(atypeFactory, leftTree),
                                        true);
                        constraintManager.addComparisonConstraint(
                                ComparisonOperationKind.GREATER_THAN_EQUAL, lhs, rhs, compThenRes);
                        ComparisonVariableSlot compElseRes =
                                slotManager.getComparisonVariableSlot(
                                        VariableAnnotator.treeToLocation(atypeFactory, leftTree),
                                        false);
                        constraintManager.addComparisonConstraint(
                                ComparisonOperationKind.LESS_THAN, lhs, rhs, compElseRes);
                    }
                    break;
                case LESS_THAN: // <
                    if (leftTree instanceof IdentifierTree) {
                        ComparisonVariableSlot compThenRes =
                                slotManager.getComparisonVariableSlot(
                                        VariableAnnotator.treeToLocation(atypeFactory, leftTree),
                                        true);
                        constraintManager.addComparisonConstraint(
                                ComparisonOperationKind.LESS_THAN, lhs, rhs, compThenRes);
                        ComparisonVariableSlot compElseRes =
                                slotManager.getComparisonVariableSlot(
                                        VariableAnnotator.treeToLocation(atypeFactory, leftTree),
                                        false);
                        constraintManager.addComparisonConstraint(
                                ComparisonOperationKind.GREATER_THAN_EQUAL, lhs, rhs, compElseRes);
                    }
                    break;
                case LESS_THAN_EQUAL: // <=
                    if (leftTree instanceof IdentifierTree) {
                        ComparisonVariableSlot compThenRes =
                                slotManager.getComparisonVariableSlot(
                                        VariableAnnotator.treeToLocation(atypeFactory, leftTree),
                                        true);
                        constraintManager.addComparisonConstraint(
                                ComparisonOperationKind.LESS_THAN_EQUAL, lhs, rhs, compThenRes);
                        ComparisonVariableSlot compElseRes =
                                slotManager.getComparisonVariableSlot(
                                        VariableAnnotator.treeToLocation(atypeFactory, leftTree),
                                        false);
                        constraintManager.addComparisonConstraint(
                                ComparisonOperationKind.GREATER_THAN, lhs, rhs, compElseRes);
                    }
                    break;
                default:
                    break;
            }
        }

        return super.visitBinary(binaryTree, p);
    }

    @Override
    public Void visitCompoundAssignment(CompoundAssignmentTree tree, Void p) {
        // infer mode, adds constraints for binary operations
        if (infer) {
            SlotManager slotManager = InferenceMain.getInstance().getSlotManager();
            ConstraintManager constraintManager =
                    InferenceMain.getInstance().getConstraintManager();

            InferenceAnnotatedTypeFactory iatf = (InferenceAnnotatedTypeFactory) atypeFactory;

            AnnotatedTypeMirror resATM = atypeFactory.getAnnotatedType(tree);
            AnnotatedTypeMirror exprATM = iatf.getAnnotatedType(tree.getExpression());
            AnnotatedTypeMirror varATM = iatf.getAnnotatedTypeLhs(tree.getVariable());
            AnnotationMirror exprAMVal = exprATM.getEffectiveAnnotationInHierarchy(UNKNOWNVAL);
            AnnotationMirror varAMVal = varATM.getEffectiveAnnotationInHierarchy(UNKNOWNVAL);
            Slot lhs = slotManager.getSlot(exprATM);
            Slot rhs = slotManager.getSlot(varATM);
            Slot res = slotManager.getSlot(resATM);

            Kind kind = tree.getKind();
            switch (kind) {
                case PLUS_ASSIGNMENT:
                    if (TreeUtils.isStringConcatenation(tree)) {
                        break;
                    }
                case MINUS_ASSIGNMENT:
                case MULTIPLY_ASSIGNMENT:
                case DIVIDE_ASSIGNMENT:
                case REMAINDER_ASSIGNMENT:
                    if (exprAMVal == null || varAMVal == null) {
                        ArithmeticVariableSlot avsResplus =
                                slotManager.getArithmeticVariableSlot(
                                        VariableAnnotator.treeToLocation(atypeFactory, tree));
                        // TODO: slot is null because location is missing. Find out why location is
                        // missing.
                        if (avsResplus == null) {
                            break;
                        }
                        constraintManager.addEqualityConstraint(avsResplus, res);
                        break;
                    }
                    if (AnnotationUtils.areSameByClass(exprAMVal, IntRange.class)
                            && AnnotationUtils.areSameByClass(varAMVal, IntRange.class)) {
                        break;
                    } // Create LUB constraint by default
                default:
                    Slot lubSlot = slotManager.getSlot(atypeFactory.getAnnotatedType(tree));
                    // Create LUB constraint by default
                    constraintManager.addSubtypeConstraint(lhs, lubSlot);
                    constraintManager.addSubtypeConstraint(rhs, lubSlot);
                    break;
            }
        }

        return super.visitCompoundAssignment(tree, p);
    }

    @Override
    public Void visitUnary(UnaryTree tree, Void p) {
        // infer mode, adds constraints for unary operations
        if (infer) {
            SlotManager slotManager = InferenceMain.getInstance().getSlotManager();
            ConstraintManager constraintManager =
                    InferenceMain.getInstance().getConstraintManager();

            ValueInferenceAnnotatedTypeFactory iatf =
                    (ValueInferenceAnnotatedTypeFactory) atypeFactory;

            Kind kind = tree.getKind();
            AnnotatedTypeMirror resType = atypeFactory.getAnnotatedType(tree.getExpression());
            AnnotationMirror exprAMVal = resType.getEffectiveAnnotationInHierarchy(UNKNOWNVAL);
            Slot var = slotManager.getSlot(resType);

            switch (kind) {
                case UNARY_MINUS:
                    if (exprAMVal == null) {
                        ArithmeticVariableSlot avsResplus =
                                slotManager.getArithmeticVariableSlot(
                                        VariableAnnotator.treeToLocation(atypeFactory, tree));
                        // TODO: slot is null because location is missing.
                        if (avsResplus == null) {
                            break;
                        }
                        ConstantSlot cs =
                                slotManager.createConstantSlot(
                                        iatf.createIntRangeAnnotation(-1, -1));
                        constraintManager.addArithmeticConstraint(
                                ArithmeticOperationKind.MULTIPLY, cs, var, avsResplus);
                        break;
                    }
                    if (AnnotationUtils.areSameByClass(exprAMVal, IntRange.class)) {
                        break;
                    } // Create LUB constraint by default
                case PREFIX_INCREMENT:
                case PREFIX_DECREMENT:
                case POSTFIX_INCREMENT:
                case POSTFIX_DECREMENT:
                    if (exprAMVal == null) {
                        ArithmeticVariableSlot avsResplus =
                                slotManager.getArithmeticVariableSlot(
                                        VariableAnnotator.treeToLocation(atypeFactory, tree));
                        // TODO: slot is null because location is missing.
                        if (avsResplus == null) {
                            break;
                        }
                        constraintManager.addEqualityConstraint(avsResplus, var);
                        if (var instanceof RefinementVariableSlot) {
                            constraintManager.addSubtypeConstraint(
                                    var, ((RefinementVariableSlot) var).getRefined());
                        }
                        return null;
                    }
                    if (AnnotationUtils.areSameByClass(exprAMVal, IntRange.class)) {
                        break;
                    }
                default:
                    // Create LUB constraint by default
                    Slot lubSlot = slotManager.getSlot(atypeFactory.getAnnotatedType(tree));
                    constraintManager.addSubtypeConstraint(var, lubSlot);
                    break;
            }
        }

        return super.visitUnary(tree, p);
    }

    @Override
    public Void visitTypeCast(TypeCastTree tree, Void p) {
        // infer mode, adds constraints for cast operations
        if (infer) {
            SlotManager slotManager = InferenceMain.getInstance().getSlotManager();
            ConstraintManager constraintManager =
                    InferenceMain.getInstance().getConstraintManager();

            InferenceAnnotatedTypeFactory iatf = (InferenceAnnotatedTypeFactory) atypeFactory;

            AnnotatedTypeMirror castATM = iatf.getAnnotatedType(tree);
            AnnotatedTypeMirror exprATM = iatf.getAnnotatedType(tree.getExpression());
            AnnotationMirror castAM = castATM.getEffectiveAnnotationInHierarchy(iatf.getVarAnnot());
            AnnotationMirror exprAM = exprATM.getEffectiveAnnotationInHierarchy(iatf.getVarAnnot());
            if (castAM == null || exprAM == null) {
                return super.visitTypeCast(tree, p);
            }
            Slot cast = slotManager.getSlot(castAM);
            Slot expr = slotManager.getSlot(exprAM);

            if (cast != null && expr != null) {
                constraintManager.addSubtypeConstraint(expr, cast);
            }
        }

        return super.visitTypeCast(tree, p);
    }
}
