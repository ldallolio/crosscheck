package net.sf.metacad.revenge.state;

import java.util.LinkedHashMap;
import java.util.Map;

import net.sf.metacad.revenge.definition.FunctionDefinition;
import net.sf.metacad.revenge.definition.FunctionSignature;
import net.sf.metacad.revenge.definition.VariableDefinition;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.MetaExpression;
import net.sf.metacad.revenge.expression.MultipleConditionedExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanOperator;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.NotExpression;
import net.sf.metacad.revenge.type.ClassType;

public class ConditionedState extends StateFilter {

	private static final long serialVersionUID = -7419021060585197040L;

	final BooleanExpression condition;

	private boolean conditioning = true;

	public ConditionedState(BooleanExpression condition, CodeState originalState) {
		super(originalState);
		this.condition = condition;
	}

	public BooleanExpression getCondition() {
		return condition;
	}

	@Override
	public void defineVariable(VariableDefinition variable) {

		if (conditioning) {
			// if (...) int a = 1; is illegal at least in java
			// if (...) {int a = 1;} is legal but this should be taken care of
			// by a block statement inside the if statement
			throw new IllegalStateException(
					"Cannot define variable : [" + variable + "] inside a : [" + this.getClass() + "]");
		} else {
			// We are no longer in the if statement, just passing through
			// if(...) {...}; int a;

			wrappedState.defineVariable(variable);
		}

	}

	@Override
	public void assignVariable(String variableName, CodeExpression newValue) {
		if (conditioning) {
			if (!wrappedState.isVariableDefined(variableName)) {
				throw new IllegalStateException(
						"CodeVariable : [" + variableName + "] not defined before entering if statement.");
			}
			CodeExpression originalCodeExpression = wrappedState.variableValue(variableName);
			Map<BooleanExpression, CodeExpression> conditionedExpressions = new LinkedHashMap<>();
			conditionedExpressions.put(condition, newValue);
			conditionedExpressions.put(NotExpression.create(condition), originalCodeExpression);
			CodeExpression multipleValue = MultipleConditionedExpression.create(conditionedExpressions);
			wrappedState.assignVariable(variableName, multipleValue);
		} else {
			wrappedState.assignVariable(variableName, newValue);
		}
	}

	public void stopConditioning() {
		// This state could not (still) have a wrapping state,
		// so "purge" alone is not enough
		conditioning = false;
	}

	public boolean isConditioning() {
		return conditioning;
	}

	@Override
	public void setReturnExpression(CodeExpression returnExpression) {
		if (conditioning) {
			Map<BooleanExpression, CodeExpression> conditionedExpressions = new LinkedHashMap<>();
			conditionedExpressions.put(condition, returnExpression);
			if (!MetaExpression.NO_RETURN_VALUE.equals(wrappedState.getReturnExpression())) {
				conditionedExpressions.put(NotExpression.create(condition), wrappedState.getReturnExpression());
			}
			wrappedState.setReturnExpression(MultipleConditionedExpression.create(conditionedExpressions));
		} else {
			wrappedState.setReturnExpression(returnExpression);
		}
	}

	@Override
	public void setBreakCondition(BooleanExpression breakCondition) {
		if (conditioning) {
			BooleanExpression inner = BinaryBooleanExpression.create(BinaryBooleanOperator.AND, condition,
					breakCondition);
			BooleanExpression original = BinaryBooleanExpression.create(BinaryBooleanOperator.AND,
					NotExpression.create(condition), wrappedState.getBreakCondition());
			wrappedState.setBreakCondition(BinaryBooleanExpression.create(BinaryBooleanOperator.OR, inner, original));
		} else {
			wrappedState.setBreakCondition(breakCondition);
		}
	}

	@Override
	public void setContinueCondition(BooleanExpression continueCondition) {
		if (conditioning) {
			BooleanExpression inner = BinaryBooleanExpression.create(BinaryBooleanOperator.AND, condition,
					continueCondition);
			BooleanExpression original = BinaryBooleanExpression.create(BinaryBooleanOperator.AND,
					NotExpression.create(condition), wrappedState.getContinueCondition());
			wrappedState
					.setContinueCondition(BinaryBooleanExpression.create(BinaryBooleanOperator.OR, inner, original));

		} else {
			wrappedState.setContinueCondition(continueCondition);
		}
	}

	@Override
	public void defineFunction(FunctionDefinition function) {
		if (conditioning) {
			// if (...) int foo() {}; is illegal at least in java
			// if (...) {int foo() {};} could be legal but this should be taken
			// care of
			// by a block statement inside the if statement
			throw new IllegalStateException(
					"Cannot define a function : [" + function.functionName + "] inside a : [" + this.getClass() + "]");
		} else {
			// We are no longer in the if statement, just passing through
			// if(...) {...}; int a;

			wrappedState.defineFunction(function);
		}
	}

	@Override
	public void defineClass(ClassType classType) {
		// When implementing, think of inline anonymous classes
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void setRecursionCondition(FunctionSignature signature, BooleanExpression newCondition) {
		if (conditioning) {
			BooleanExpression conditioned = BinaryBooleanExpression.create(BinaryBooleanOperator.AND, newCondition,
					condition);
			BooleanExpression previous = BinaryBooleanExpression.create(BinaryBooleanOperator.AND,
					wrappedState.getRecursionCondition(signature), NotExpression.create(condition));
			BooleanExpression composedCondition = BinaryBooleanExpression.create(BinaryBooleanOperator.OR, conditioned,
					previous);
			wrappedState.setRecursionCondition(signature, composedCondition);
		} else {
			wrappedState.setRecursionCondition(signature, newCondition);
		}
	}

	@Override
	public CodeExpression recursionCall(String functionName, CodeExpression[] parameterValues) {
		if (conditioning) {
			CodeExpression multipleValue = MultipleConditionedExpression.create(condition,
					wrappedState.recursionCall(functionName, parameterValues));
			return multipleValue;
		} else {
			return wrappedState.recursionCall(functionName, parameterValues);
		}
	}

}
