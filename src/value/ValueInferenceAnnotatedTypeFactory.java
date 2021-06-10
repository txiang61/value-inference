package value;

import checkers.inference.InferenceAnnotatedTypeFactory;
import checkers.inference.InferenceChecker;
import checkers.inference.InferenceMain;
import checkers.inference.InferenceQualifierHierarchy;
import checkers.inference.InferenceTreeAnnotator;
import checkers.inference.InferrableChecker;
import checkers.inference.SlotManager;
import checkers.inference.VariableAnnotator;
import checkers.inference.model.AnnotationLocation;
import checkers.inference.model.ArithmeticConstraint.ArithmeticOperationKind;
import checkers.inference.model.ArithmeticVariableSlot;
import checkers.inference.model.ConstantSlot;
import checkers.inference.model.ConstraintManager;
import checkers.inference.model.Slot;
import checkers.inference.qual.VarAnnot;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.ExpressionTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.MemberSelectTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.NewClassTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.Tree.Kind;
import com.sun.source.tree.UnaryTree;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.value.ValueCheckerUtils;
import org.checkerframework.common.value.util.Range;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.AnnotatedTypes;
import org.checkerframework.framework.util.MultiGraphQualifierHierarchy.MultiGraphFactory;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.Pair;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.TypesUtils;
import value.qual.BoolVal;
import value.qual.BottomVal;
import value.qual.IntRange;
import value.qual.StringVal;
import value.qual.UnknownVal;

public class ValueInferenceAnnotatedTypeFactory extends InferenceAnnotatedTypeFactory {

    /** The top type for this hierarchy. */
    protected final AnnotationMirror UNKNOWNVAL =
            AnnotationBuilder.fromClass(elements, UnknownVal.class);

    /** The bottom type for this hierarchy. */
    protected final AnnotationMirror BOTTOMVAL =
            AnnotationBuilder.fromClass(elements, BottomVal.class);

    public ValueInferenceAnnotatedTypeFactory(
            InferenceChecker inferenceChecker,
            boolean withCombineConstraints,
            BaseAnnotatedTypeFactory realTypeFactory,
            InferrableChecker realChecker,
            SlotManager slotManager,
            ConstraintManager constraintManager) {
        super(
                inferenceChecker,
                withCombineConstraints,
                realTypeFactory,
                realChecker,
                slotManager,
                constraintManager);
        postInit();
    }

    @Override
    public TreeAnnotator createTreeAnnotator() {
        return new ListTreeAnnotator(
                new ValueInferenceTreeAnnotator(
                        this, realChecker, realTypeFactory, variableAnnotator, slotManager));
    }

    protected class ValueInferenceTreeAnnotator extends InferenceTreeAnnotator {
        public ValueInferenceTreeAnnotator(
                InferenceAnnotatedTypeFactory atypeFactory,
                InferrableChecker realChecker,
                AnnotatedTypeFactory realAnnotatedTypeFactory,
                VariableAnnotator variableAnnotator,
                SlotManager slotManager) {
            super(
                    atypeFactory,
                    realChecker,
                    realAnnotatedTypeFactory,
                    variableAnnotator,
                    slotManager);
        }

        @Override
        public Void visitUnary(UnaryTree node, AnnotatedTypeMirror type) {
            if (node.getKind() == Kind.UNARY_MINUS) {
                variableAnnotator.visit(type, node);
                return null;
            }
            return super.visitUnary(node, type);
        }

        //        @Override
        //        public Void visitCompoundAssignment(CompoundAssignmentTree node,
        // AnnotatedTypeMirror type) {
        //            variableAnnotator.visit(type, node);
        //            return super.visitCompoundAssignment(node, type);
        //        }

        @Override
        public Void visitLiteral(final LiteralTree tree, AnnotatedTypeMirror type) {
            Object value = tree.getValue();
            switch (tree.getKind()) {
                case NULL_LITERAL:
                    replaceATM(type, BOTTOMVAL);
                    return null;
                    //                case BOOLEAN_LITERAL:
                    //                    AnnotationMirror boolAnno =
                    //
                    // createBooleanAnnotation(Collections.singletonList((Boolean) value));
                    //                    replaceATM(type, boolAnno);
                    //                    return null;
                case CHAR_LITERAL:
                    AnnotationMirror charAnno =
                            createCharAnnotation(Collections.singletonList((Character) value));
                    replaceATM(type, charAnno);
                    return null;
                case INT_LITERAL:
                case LONG_LITERAL:
                    AnnotationMirror numberAnno =
                            createNumberAnnotationMirror(Collections.singletonList((Number) value));
                    replaceATM(type, numberAnno);
                    return null;
                case DOUBLE_LITERAL:
                case FLOAT_LITERAL:
                    replaceATM(type, UNKNOWNVAL);
                    return null;
                    //                case STRING_LITERAL:
                    //                    AnnotationMirror stringAnno =
                    //
                    // createStringAnnotation(Collections.singletonList((String) value));
                    //                    replaceATM(type, stringAnno);
                    //                    return null;
                default:
                    return null;
            }
        }

        @Override
        public Void visitNewClass(NewClassTree newClassTree, AnnotatedTypeMirror atm) {
            // Call super to replace polymorphic annotations with fresh variable slots
            super.visitNewClass(newClassTree, atm);

            if (isConstructorDeclaredWithPolymorphicReturn(newClassTree)) {
                // 1) the variable slot generated for the polymorphic declared return type
                Slot varSlotForPolyReturn = variableAnnotator.getOrCreatePolyVar(newClassTree);

                // 2) the call site return type: "@m" in "new @m Clazz(...)"
                Slot callSiteReturnVarSlot = slotManager.getSlot(atm);

                // Create a subtype constraint: callSiteReturnVarSlot <: varSlotForPolyReturn
                // since after annotation insertion, the varSlotForPolyReturn is conceptually a
                // cast of the newly created object:
                // "(@varSlotForPolyReturn Clazz) new @m Clazz(...)"
                constraintManager.addSubtypeConstraint(callSiteReturnVarSlot, varSlotForPolyReturn);

                // Replace the slot/annotation in the atm (callSiteReturnVarSlot) with the
                // varSlotForPolyReturn for upstream analysis
                atm.replaceAnnotation(slotManager.getAnnotation(varSlotForPolyReturn));
            }

            return null;
        }

        @Override
        public Void visitMethodInvocation(
                MethodInvocationTree methodInvocationTree, AnnotatedTypeMirror atm) {
            super.visitMethodInvocation(methodInvocationTree, atm);

            if (isMethodDeclaredWithPolymorphicReturn(methodInvocationTree)) {
                variableAnnotator.getOrCreatePolyVar(methodInvocationTree);
            }

            return null;
        }

        private void replaceATM(AnnotatedTypeMirror atm, AnnotationMirror am) {
            final ConstantSlot cs = slotManager.createConstantSlot(am);
            AnnotationBuilder ab =
                    new AnnotationBuilder(realTypeFactory.getProcessingEnv(), VarAnnot.class);
            ab.setValue("value", cs.getId());
            atm.replaceAnnotation(ab.build());
        }

        // see if given annotation mirror is the VarAnnot versions of @PolyVal
        private boolean isPolyAnnotation(AnnotationMirror annot) {
            Slot slot = slotManager.getSlot(annot);
            if (slot instanceof ConstantSlot) {
                AnnotationMirror constant = ((ConstantSlot) slot).getValue();
                return InferenceQualifierHierarchy.isPolymorphic(constant);
            }
            return false;
        }

        // based on InferenceATF.constructorFromUse()
        private boolean isConstructorDeclaredWithPolymorphicReturn(NewClassTree newClassTree) {
            final ExecutableElement constructorElem = TreeUtils.constructor(newClassTree);
            final AnnotatedTypeMirror constructorReturnType = fromNewClass(newClassTree);
            final AnnotatedExecutableType constructorType =
                    AnnotatedTypes.asMemberOf(
                            types,
                            ValueInferenceAnnotatedTypeFactory.this,
                            constructorReturnType,
                            constructorElem);

            // if any of the annotations on the return type of the constructor is a
            // polymorphic annotation, return true
            for (AnnotationMirror annot : constructorType.getReturnType().getAnnotations()) {
                if (isPolyAnnotation(annot)) {
                    return true;
                }
            }

            return false;
        }

        // based on InferenceATF.methodFromUse()
        private boolean isMethodDeclaredWithPolymorphicReturn(
                MethodInvocationTree methodInvocationTree) {
            final ExecutableElement methodElem = TreeUtils.elementFromUse(methodInvocationTree);
            // final AnnotatedExecutableType methodType = getAnnotatedType(methodElem);

            final ExpressionTree methodSelectExpression = methodInvocationTree.getMethodSelect();
            final AnnotatedTypeMirror receiverType;
            if (methodSelectExpression.getKind() == Tree.Kind.MEMBER_SELECT) {
                receiverType =
                        getAnnotatedType(
                                ((MemberSelectTree) methodSelectExpression).getExpression());
            } else {
                receiverType = getSelfType(methodInvocationTree);
            }

            final AnnotatedExecutableType methodOfReceiver =
                    AnnotatedTypes.asMemberOf(
                            types,
                            ValueInferenceAnnotatedTypeFactory.this,
                            receiverType,
                            methodElem);

            // if any of the annotations on the return type of the constructor is a
            // polymorphic annotation, return true
            for (AnnotationMirror annot : methodOfReceiver.getReturnType().getAnnotations()) {
                if (isPolyAnnotation(annot)) {
                    return true;
                }
            }

            return false;
        }
    }

    @Override
    public QualifierHierarchy createQualifierHierarchy(MultiGraphFactory factory) {
        return new ValueInferenceQualifierHierarchy(factory);
    }

    private final class ValueInferenceQualifierHierarchy extends InferenceQualifierHierarchy {
        public ValueInferenceQualifierHierarchy(MultiGraphFactory multiGraphFactory) {
            super(multiGraphFactory);
        }

        @Override
        public Set<? extends AnnotationMirror> leastUpperBounds(
                Collection<? extends AnnotationMirror> annos1,
                Collection<? extends AnnotationMirror> annos2) {
            // TODO: remove hack
            Set<AnnotationMirror> result = AnnotationUtils.createAnnotationSet();
            for (AnnotationMirror a1 : annos1) {
                for (AnnotationMirror a2 : annos2) {
                    AnnotationMirror lub = leastUpperBound(a1, a2);
                    if (lub != null) {
                        result.add(lub);
                    }
                }
            }
            return result;
        }
    }

    /**
     * The domain of the Constant Value Checker: the types for which it estimates possible values.
     */
    protected static final Set<String> COVERED_CLASS_STRINGS =
            Collections.unmodifiableSet(
                    new HashSet<>(
                            Arrays.asList(
                                    "int",
                                    "java.lang.Integer",
                                    "double",
                                    "java.lang.Double",
                                    "byte",
                                    "java.lang.Byte",
                                    //                                    "java.lang.String",
                                    "char",
                                    "java.lang.Character",
                                    "float",
                                    "java.lang.Float",
                                    //                                    "boolean",
                                    //                                    "java.lang.Boolean",
                                    "long",
                                    "java.lang.Long",
                                    "short",
                                    "java.lang.Short",
                                    "char[]")));

    @Override
    public VariableAnnotator createVariableAnnotator() {
        return new ValueVariableAnnotator(
                this, realTypeFactory, realChecker, slotManager, constraintManager);
    }

    private final class ValueVariableAnnotator extends VariableAnnotator {
        public ValueVariableAnnotator(
                InferenceAnnotatedTypeFactory typeFactory,
                AnnotatedTypeFactory realTypeFactory,
                InferrableChecker realChecker,
                SlotManager slotManager,
                ConstraintManager constraintManager) {
            super(typeFactory, realTypeFactory, realChecker, slotManager, constraintManager);
        }

        @Override
        public void handleBinaryTree(AnnotatedTypeMirror atm, BinaryTree binaryTree) {
            // Super creates an LUB constraint by default, we create an VariableSlot here
            // instead for the result of the binary op and create LUB constraint

            // create varslot for the result of the binary tree computation
            // note: constraints for binary ops are added in Visitor
            if (this.treeToVarAnnoPair.containsKey(binaryTree)) {
                atm.replaceAnnotations(
                        (Iterable) ((Pair) this.treeToVarAnnoPair.get(binaryTree)).second);
            } else {
                // TODO: find out why there are missing location
                AnnotationLocation location =
                        VariableAnnotator.treeToLocation(inferenceTypeFactory, binaryTree);
                if (location == AnnotationLocation.MISSING_LOCATION) {
                    return;
                }
                if (atm.getUnderlyingType().getKind() == TypeKind.DOUBLE
                        || atm.getUnderlyingType().getKind() == TypeKind.FLOAT) {
                    return;
                }
                ConstraintManager constraintManager =
                        InferenceMain.getInstance().getConstraintManager();
                AnnotatedTypeMirror lhsATM =
                        this.inferenceTypeFactory.getAnnotatedType(binaryTree.getLeftOperand());
                AnnotatedTypeMirror rhsATM =
                        this.inferenceTypeFactory.getAnnotatedType(binaryTree.getRightOperand());

                AnnotationMirror lhsAM = lhsATM.getEffectiveAnnotationInHierarchy(UNKNOWNVAL);
                AnnotationMirror rhsAM = rhsATM.getEffectiveAnnotationInHierarchy(UNKNOWNVAL);
                // grab slots for the component (only for lub slot)
                Slot lhs = slotManager.getSlot(lhsATM);
                Slot rhs = slotManager.getSlot(rhsATM);

                Slot result;
                Kind kind = binaryTree.getKind();
                switch (kind) {
                    case PLUS:
                        if (TreeUtils.isStringConcatenation(binaryTree)) {
                            result = slotManager.createConstantSlot(UNKNOWNVAL);
                            //                            result =
                            //                                    slotManager.createConstantSlot(
                            //
                            // AnnotationBuilder.fromClass(elements, StringVal.class));
                            break;
                        }
                        if (lhsAM == null || rhsAM == null) {
                            result = slotManager.createArithmeticVariableSlot(location);
                            ArithmeticOperationKind opKindplus =
                                    ArithmeticOperationKind.fromTreeKind(kind);
                            constraintManager.addArithmeticConstraint(
                                    opKindplus, lhs, rhs, (ArithmeticVariableSlot) result);
                            break;
                        }
                        if (AnnotationUtils.areSameByClass(lhsAM, IntRange.class)
                                && AnnotationUtils.areSameByClass(rhsAM, IntRange.class)) {
                            Range range = getRange(lhsAM).plus(getRange(rhsAM));
                            if (range.isLongEverything() && atm.getKind() == TypeKind.INT) {
                                range = Range.INT_EVERYTHING;
                            }
                            result =
                                    slotManager.createConstantSlot(createIntRangeAnnotation(range));
                            break;
                        }
                        result = slotManager.createLubVariableSlot(lhs, rhs);
                        break;
                    case MINUS:
                        if (lhsAM == null || rhsAM == null) {
                            result = slotManager.createArithmeticVariableSlot(location);
                            ArithmeticOperationKind opKindplus =
                                    ArithmeticOperationKind.fromTreeKind(kind);
                            constraintManager.addArithmeticConstraint(
                                    opKindplus, lhs, rhs, (ArithmeticVariableSlot) result);
                            break;
                        }
                        if (AnnotationUtils.areSameByClass(lhsAM, IntRange.class)
                                && AnnotationUtils.areSameByClass(rhsAM, IntRange.class)) {
                            Range range = getRange(lhsAM).minus(getRange(rhsAM));
                            if (range.isLongEverything() && atm.getKind() == TypeKind.INT) {
                                range = Range.INT_EVERYTHING;
                            }
                            result =
                                    slotManager.createConstantSlot(createIntRangeAnnotation(range));
                            break;
                        }
                        result = slotManager.createLubVariableSlot(lhs, rhs);
                        break;
                    case MULTIPLY:
                        if (lhsAM == null || rhsAM == null) {
                            result = slotManager.createArithmeticVariableSlot(location);
                            ArithmeticOperationKind opKindplus =
                                    ArithmeticOperationKind.fromTreeKind(kind);
                            constraintManager.addArithmeticConstraint(
                                    opKindplus, lhs, rhs, (ArithmeticVariableSlot) result);
                            break;
                        }
                        if (AnnotationUtils.areSameByClass(lhsAM, IntRange.class)
                                && AnnotationUtils.areSameByClass(rhsAM, IntRange.class)) {
                            Range range = getRange(lhsAM).times(getRange(rhsAM));
                            if (range.isLongEverything() && atm.getKind() == TypeKind.INT) {
                                range = Range.INT_EVERYTHING;
                            }
                            result =
                                    slotManager.createConstantSlot(createIntRangeAnnotation(range));
                            break;
                        }
                        result = slotManager.createLubVariableSlot(lhs, rhs);
                        break;
                    case DIVIDE:
                        if (lhsAM == null || rhsAM == null) {
                            result = slotManager.createArithmeticVariableSlot(location);
                            ArithmeticOperationKind opKindplus =
                                    ArithmeticOperationKind.fromTreeKind(kind);
                            constraintManager.addArithmeticConstraint(
                                    opKindplus, lhs, rhs, (ArithmeticVariableSlot) result);
                            break;
                        }
                        if (AnnotationUtils.areSameByClass(lhsAM, IntRange.class)
                                && AnnotationUtils.areSameByClass(rhsAM, IntRange.class)) {
                            Range range = getRange(lhsAM).divide(getRange(rhsAM));
                            if (range.isLongEverything() && atm.getKind() == TypeKind.INT) {
                                range = Range.INT_EVERYTHING;
                            }
                            result =
                                    slotManager.createConstantSlot(createIntRangeAnnotation(range));
                            break;
                        }
                        result = slotManager.createLubVariableSlot(lhs, rhs);
                        break;
                    case REMAINDER:
                        if (lhsAM == null || rhsAM == null) {
                            result = slotManager.createArithmeticVariableSlot(location);
                            ArithmeticOperationKind opKindplus =
                                    ArithmeticOperationKind.fromTreeKind(kind);
                            constraintManager.addArithmeticConstraint(
                                    opKindplus, lhs, rhs, (ArithmeticVariableSlot) result);
                            break;
                        }
                        if (AnnotationUtils.areSameByClass(lhsAM, IntRange.class)
                                && AnnotationUtils.areSameByClass(rhsAM, IntRange.class)) {
                            Range range = getRange(lhsAM).remainder(getRange(rhsAM));
                            if (range.isLongEverything() && atm.getKind() == TypeKind.INT) {
                                range = Range.INT_EVERYTHING;
                            }
                            result =
                                    slotManager.createConstantSlot(createIntRangeAnnotation(range));
                            break;
                        }
                        result = slotManager.createLubVariableSlot(lhs, rhs);
                        break;
                    case LEFT_SHIFT:
                        if (lhsAM == null || rhsAM == null) {
                            result = slotManager.createArithmeticVariableSlot(location);
                            ArithmeticOperationKind opKindplus =
                                    ArithmeticOperationKind.fromTreeKind(kind);
                            constraintManager.addArithmeticConstraint(
                                    opKindplus, lhs, rhs, (ArithmeticVariableSlot) result);
                            break;
                        }
                        if (AnnotationUtils.areSameByClass(lhsAM, IntRange.class)
                                && AnnotationUtils.areSameByClass(rhsAM, IntRange.class)) {
                            Range range = getRange(lhsAM).shiftLeft(getRange(rhsAM));
                            if (range.isLongEverything() && atm.getKind() == TypeKind.INT) {
                                range = Range.INT_EVERYTHING;
                            }
                            result =
                                    slotManager.createConstantSlot(createIntRangeAnnotation(range));
                            break;
                        }
                        result = slotManager.createLubVariableSlot(lhs, rhs);
                        break;
                    case RIGHT_SHIFT:
                        if (lhsAM == null || rhsAM == null) {
                            result = slotManager.createArithmeticVariableSlot(location);
                            ArithmeticOperationKind opKindplus =
                                    ArithmeticOperationKind.fromTreeKind(kind);
                            constraintManager.addArithmeticConstraint(
                                    opKindplus, lhs, rhs, (ArithmeticVariableSlot) result);
                            break;
                        }
                        if (AnnotationUtils.areSameByClass(lhsAM, IntRange.class)
                                && AnnotationUtils.areSameByClass(rhsAM, IntRange.class)) {
                            Range range = getRange(lhsAM).signedShiftRight(getRange(rhsAM));
                            if (range.isLongEverything() && atm.getKind() == TypeKind.INT) {
                                range = Range.INT_EVERYTHING;
                            }
                            result =
                                    slotManager.createConstantSlot(createIntRangeAnnotation(range));
                            break;
                        }
                        result = slotManager.createLubVariableSlot(lhs, rhs);
                        break;
                    case UNSIGNED_RIGHT_SHIFT:
                        if (lhsAM == null || rhsAM == null) {
                            result = slotManager.createArithmeticVariableSlot(location);
                            ArithmeticOperationKind opKindplus =
                                    ArithmeticOperationKind.fromTreeKind(kind);
                            constraintManager.addArithmeticConstraint(
                                    opKindplus, lhs, rhs, (ArithmeticVariableSlot) result);
                            break;
                        }
                        if (AnnotationUtils.areSameByClass(lhsAM, IntRange.class)
                                && AnnotationUtils.areSameByClass(rhsAM, IntRange.class)) {
                            Range range = getRange(lhsAM).unsignedShiftRight(getRange(rhsAM));
                            if (range.isLongEverything() && atm.getKind() == TypeKind.INT) {
                                range = Range.INT_EVERYTHING;
                            }
                            result =
                                    slotManager.createConstantSlot(createIntRangeAnnotation(range));
                            break;
                        }
                        result = slotManager.createLubVariableSlot(lhs, rhs);
                        break;
                    case AND:
                        if (lhsAM == null || rhsAM == null) {
                            result = slotManager.createArithmeticVariableSlot(location);
                            ArithmeticOperationKind opKindplus =
                                    ArithmeticOperationKind.fromTreeKind(kind);
                            constraintManager.addArithmeticConstraint(
                                    opKindplus, lhs, rhs, (ArithmeticVariableSlot) result);
                            break;
                        }
                        if (AnnotationUtils.areSameByClass(lhsAM, IntRange.class)
                                && AnnotationUtils.areSameByClass(rhsAM, IntRange.class)) {
                            Range range = getRange(lhsAM).bitwiseAnd(getRange(rhsAM));
                            if (range.isLongEverything() && atm.getKind() == TypeKind.INT) {
                                range = Range.INT_EVERYTHING;
                            }
                            result =
                                    slotManager.createConstantSlot(createIntRangeAnnotation(range));
                            break;
                        }
                        result = slotManager.createLubVariableSlot(lhs, rhs);
                        break;
                    case OR:
                        if (lhsAM == null || rhsAM == null) {
                            result = slotManager.createArithmeticVariableSlot(location);
                            ArithmeticOperationKind opKindplus =
                                    ArithmeticOperationKind.fromTreeKind(kind);
                            constraintManager.addArithmeticConstraint(
                                    opKindplus, lhs, rhs, (ArithmeticVariableSlot) result);
                            break;
                        }
                        if (AnnotationUtils.areSameByClass(lhsAM, IntRange.class)
                                && AnnotationUtils.areSameByClass(rhsAM, IntRange.class)) {
                            Range range = getRange(lhsAM).bitwiseOr(getRange(rhsAM));
                            if (range.isLongEverything() && atm.getKind() == TypeKind.INT) {
                                range = Range.INT_EVERYTHING;
                            }
                            result =
                                    slotManager.createConstantSlot(createIntRangeAnnotation(range));
                            break;
                        }
                        result = slotManager.createLubVariableSlot(lhs, rhs);
                        break;
                    case XOR:
                        if (lhsAM == null || rhsAM == null) {
                            result = slotManager.createArithmeticVariableSlot(location);
                            ArithmeticOperationKind opKindplus =
                                    ArithmeticOperationKind.fromTreeKind(kind);
                            constraintManager.addArithmeticConstraint(
                                    opKindplus, lhs, rhs, (ArithmeticVariableSlot) result);
                            break;
                        }
                        if (AnnotationUtils.areSameByClass(lhsAM, IntRange.class)
                                && AnnotationUtils.areSameByClass(rhsAM, IntRange.class)) {
                            Range range = getRange(lhsAM).bitwiseXor(getRange(rhsAM));
                            if (range.isLongEverything() && atm.getKind() == TypeKind.INT) {
                                range = Range.INT_EVERYTHING;
                            }
                            result =
                                    slotManager.createConstantSlot(createIntRangeAnnotation(range));
                            break;
                        }
                        result = slotManager.createLubVariableSlot(lhs, rhs);
                        break;
                    case GREATER_THAN:
                    case GREATER_THAN_EQUAL:
                    case LESS_THAN:
                    case LESS_THAN_EQUAL:
                    case EQUAL_TO:
                    case NOT_EQUAL_TO:
                        result = slotManager.createConstantSlot(UNKNOWNVAL);
                        break;
                    default:
                        result = slotManager.createLubVariableSlot(lhs, rhs);
                        break;
                }

                // insert varAnnot of the slot into the ATM
                AnnotationMirror resultAM = slotManager.getAnnotation(result);
                atm.clearAnnotations();
                atm.replaceAnnotation(resultAM);

                Set<AnnotationMirror> resultSet = AnnotationUtils.createAnnotationSet();
                resultSet.add(resultAM);
                final Pair<Slot, Set<? extends AnnotationMirror>> varATMPair =
                        Pair.of(slotManager.getSlot(atm), resultSet);
                treeToVarAnnoPair.put(binaryTree, varATMPair);
            }
        }
    }

    /** Returns true iff the given type is in the domain of the Constant Value Checker. */
    private boolean handledByValueChecker(AnnotatedTypeMirror type) {
        TypeMirror tm = type.getUnderlyingType();
        return COVERED_CLASS_STRINGS.contains(tm.toString());
    }

    /**
     * Returns a constant value annotation with the {@code values}. The class of the annotation
     * reflects the {@code resultType} given.
     *
     * @param resultType used to selected which kind of value annotation is returned
     * @param values must be a homogeneous list: every element of it has the same class
     * @return a constant value annotation with the {@code values}
     */
    AnnotationMirror createResultingAnnotation(TypeMirror resultType, List<?> values) {
        if (values == null) {
            return UNKNOWNVAL;
        }
        // For some reason null is included in the list of values,
        // so remove it so that it does not cause a NPE elsewhere.
        values.remove(null);
        if (values.isEmpty()) {
            return BOTTOMVAL;
        }

        if (TypesUtils.isString(resultType)) {
            List<String> stringVals = new ArrayList<>(values.size());
            for (Object o : values) {
                stringVals.add((String) o);
            }
            return createStringAnnotation(stringVals);
        } else if (ValueCheckerUtils.getClassFromType(resultType) == char[].class) {
            List<String> stringVals = new ArrayList<>(values.size());
            for (Object o : values) {
                if (o instanceof char[]) {
                    stringVals.add(new String((char[]) o));
                } else {
                    stringVals.add(o.toString());
                }
            }
            return createStringAnnotation(stringVals);
        }

        TypeKind primitiveKind;
        if (TypesUtils.isPrimitive(resultType)) {
            primitiveKind = resultType.getKind();
        } else if (TypesUtils.isBoxedPrimitive(resultType)) {
            primitiveKind = types.unboxedType(resultType).getKind();
        } else {
            return UNKNOWNVAL;
        }

        switch (primitiveKind) {
            case BOOLEAN:
                List<Boolean> boolVals = new ArrayList<>(values.size());
                for (Object o : values) {
                    boolVals.add((Boolean) o);
                }
                return createBooleanAnnotation(boolVals);
            case INT:
            case LONG:
            case SHORT:
            case BYTE:
                List<Number> numberVals = new ArrayList<>(values.size());
                List<Character> characterVals = new ArrayList<>(values.size());
                for (Object o : values) {
                    if (o instanceof Character) {
                        characterVals.add((Character) o);
                    } else {
                        numberVals.add((Number) o);
                    }
                }
                if (numberVals.isEmpty()) {
                    return createCharAnnotation(characterVals);
                }
                return createNumberAnnotationMirror(new ArrayList<>(numberVals));
            case CHAR:
                List<Character> charVals = new ArrayList<>(values.size());
                for (Object o : values) {
                    if (o instanceof Number) {
                        charVals.add((char) ((Number) o).intValue());
                    } else {
                        charVals.add((char) o);
                    }
                }
                return createCharAnnotation(charVals);
            default:
                throw new UnsupportedOperationException("Unexpected kind:" + resultType);
        }
    }

    /**
     * Returns a {@link BoolVal} annotation using the values. If {@code values} is null, then
     * UnknownVal is returned; if {@code values} is empty, then bottom is returned. The values are
     * sorted and duplicates are removed before the annotation is created.
     *
     * @param values list of booleans; duplicates are allowed and the values may be in any order
     * @return a {@link BoolVal} annotation using the values
     */
    public AnnotationMirror createBooleanAnnotation(List<Boolean> values) {
        if (values == null) {
            return UNKNOWNVAL;
        }
        if (values.isEmpty()) {
            return BOTTOMVAL;
        }

        AnnotationBuilder builder = new AnnotationBuilder(processingEnv, BoolVal.class);
        return builder.build();
    }

    /** @param values must be a homogeneous list: every element of it has the same class. */
    public AnnotationMirror createNumberAnnotationMirror(List<Number> values) {
        if (values == null) {
            return UNKNOWNVAL;
        } else if (values.isEmpty()) {
            return BOTTOMVAL;
        }
        Number first = values.get(0);
        // TODO: handle double and float separately
        if (first instanceof Integer
                || first instanceof Short
                || first instanceof Long
                || first instanceof Byte) {
            List<Long> intValues = new ArrayList<>();
            for (Number number : values) {
                intValues.add(number.longValue());
            }
            return createIntValAnnotation(intValues);
        }
        throw new UnsupportedOperationException(
                "ValueAnnotatedTypeFactory: unexpected class: " + first.getClass());
    }

    /**
     * Returns a {@link StringVal} annotation using the values. If {@code values} is null, then
     * UnknownVal is returned; if {@code values} is empty, then bottom is returned. The values are
     * sorted and duplicates are removed before the annotation is created. If values is larger than
     * the max number of values allowed (10 by default), then an {@link ArrayLen} or an {@link
     * ArrayLenRange} annotation is returned.
     *
     * @param values list of strings; duplicates are allowed and the values may be in any order
     * @return a {@link StringVal} annotation using the values
     */
    public AnnotationMirror createStringAnnotation(List<String> values) {
        if (values == null) {
            return UNKNOWNVAL;
        }
        if (values.isEmpty()) {
            return BOTTOMVAL;
        }
        AnnotationBuilder builder = new AnnotationBuilder(processingEnv, StringVal.class);
        return builder.build();
    }

    /**
     * Returns a {@link IntVal} annotation using the values. If {@code values} is null, then
     * UnknownVal is returned; if {@code values} is empty, then bottom is returned. The values are
     * sorted and duplicates are removed before the annotation is created.
     *
     * @param values list of characters; duplicates are allowed and the values may be in any order
     * @return a {@link IntVal} annotation using the values
     */
    public AnnotationMirror createCharAnnotation(List<Character> values) {
        if (values == null) {
            return UNKNOWNVAL;
        }
        if (values.isEmpty()) {
            return BOTTOMVAL;
        }
        List<Long> longValues = new ArrayList<>();
        for (char value : values) {
            longValues.add((long) value);
        }
        return createIntValAnnotation(longValues);
    }

    /**
     * Returns a {@link IntVal} or {@link IntRange} annotation using the values. If {@code values}
     * is null, then UnknownVal is returned; if {@code values} is empty, then bottom is returned. If
     * the number of {@code values} is greater than MAX_VALUES, return an {@link IntRange}. In other
     * cases, the values are sorted and duplicates are removed before an {@link IntVal} is created.
     *
     * @param values list of longs; duplicates are allowed and the values may be in any order
     * @return an annotation depends on the values
     */
    public AnnotationMirror createIntValAnnotation(List<Long> values) {
        if (values == null) {
            return UNKNOWNVAL;
        }
        if (values.isEmpty()) {
            return BOTTOMVAL;
        }
        long valMin = Collections.min(values);
        long valMax = Collections.max(values);
        return createIntRangeAnnotation(valMin, valMax);
    }

    /**
     * Create an {@code @IntRange} annotation from the two (inclusive) bounds. Does not return
     * BOTTOMVAL or UNKNOWNVAL.
     */
    public AnnotationMirror createIntRangeAnnotation(long from, long to) {
        assert from <= to;
        AnnotationBuilder builder = new AnnotationBuilder(processingEnv, IntRange.class);
        builder.setValue("from", from);
        builder.setValue("to", to);
        return builder.build();
    }

    /**
     * Create an {@code @IntRange} or {@code @IntVal} annotation from the range. May return
     * BOTTOMVAL or UNKNOWNVAL.
     */
    public AnnotationMirror createIntRangeAnnotation(Range range) {
        if (range.isNothing()) {
            return BOTTOMVAL;
        } else if (range.isLongEverything()) {
            return UNKNOWNVAL;
        } else {
            return createIntRangeAnnotation(range.from, range.to);
        }
    }

    /**
     * If {@code anno} is equalient to UnknownVal, return UnknownVal; otherwise, return {@code
     * anno}.
     */
    private AnnotationMirror convertToUnknown(AnnotationMirror anno) {
        if (AnnotationUtils.areSameByClass(anno, IntRange.class)) {
            long from = AnnotationUtils.getElementValue(anno, "from", Long.class, true);
            long to = AnnotationUtils.getElementValue(anno, "to", Long.class, true);
            if (from == Long.MIN_VALUE && to == Long.MAX_VALUE) {
                return UNKNOWNVAL;
            }
        }
        return anno;
    }

    /**
     * Returns a {@code Range} bounded by the values specified in the given {@code @Range}
     * annotation. Also returns an appropriate range if an {@code @IntVal} annotation is passed.
     * Returns {@code null} if the annotation is null or if the annotation is not an {@code
     * IntRange}, {@code IntRangeFromPositive}, {@code IntVal}, or {@code ArrayLenRange}.
     */
    public Range getRange(AnnotationMirror rangeAnno) {
        if (rangeAnno == null) {
            return null;
        }

        // Assume rangeAnno is well-formed, i.e., 'from' is less than or equal to 'to'.
        if (AnnotationUtils.areSameByClass(rangeAnno, IntRange.class)) {
            return Range.create(
                    AnnotationUtils.getElementValue(rangeAnno, "from", Long.class, true),
                    AnnotationUtils.getElementValue(rangeAnno, "to", Long.class, true));
        }

        return null;
    }
}
