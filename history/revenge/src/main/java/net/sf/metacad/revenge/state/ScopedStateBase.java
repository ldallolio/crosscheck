package net.sf.metacad.revenge.state;

import java.util.HashSet;
import java.util.Set;

import net.sf.metacad.revenge.definition.FunctionDefinition;
import net.sf.metacad.revenge.definition.FunctionSignature;
import net.sf.metacad.revenge.definition.VariableDefinition;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.type.ClassType;

public abstract class ScopedStateBase extends WrappingStateBase {

	private static final long serialVersionUID = -7359513232994890838L;
	protected CodeState scopeState = new ProgramState();

	public ScopedStateBase(CodeState wrappedState) {
		super(wrappedState);
	}

	public CodeState getWrappedState() {
		return wrappedState;
	}

	public void setOuterState(CodeState outerState) {
		wrappedState = outerState;
	}

	@Override
	public CodeExpression variableValue(String variableName) {
		CodeExpression variableValue;
		if (wrapping && scopeState.isVariableDefined(variableName)) {

			// when scoping, existing scoped variables have precedence over
			// outer variables
			variableValue = scopeState.variableValue(variableName);
		} else {

			variableValue = wrappedState.variableValue(variableName);
		}
		return variableValue;
	}

	@Override
	public void assignVariable(String variableName, CodeExpression newValue) {

		if (wrapping && scopeState.isVariableDefined(variableName)) {

			// When scoping, assignment over scoped variables must win over
			// outer variables
			scopeState.assignVariable(variableName, newValue);
		} else {

			wrappedState.assignVariable(variableName, newValue);
		}
	}

	public boolean isWrapping() {
		return wrapping;
	}

	@Override
	public void defineVariable(VariableDefinition variable) {

		if (wrapping) {
			// When scoping, every definition becomes a scoped variable
			scopeState.defineVariable(variable);
		} else {

			wrappedState.defineVariable(variable);
		}
	}

	@Override
	public boolean isVariableDefined(String variableName) {
		boolean defined;
		if (wrapping) {
			defined = scopeState.isVariableDefined(variableName) || wrappedState.isVariableDefined(variableName);
		} else {
			defined = wrappedState.isVariableDefined(variableName);
		}

		return defined;
	}

	public boolean isLocallyDefined(String variableName) {
		return wrapping && scopeState.isVariableDefined(variableName);
	}

	public boolean isGloballyDefined(String variableName) {
		return wrappedState.isVariableDefined(variableName);
	}

	@Override
	public CodeExpression getLeftValue() {
		CodeExpression leftValue;

		if (wrapping) {
			leftValue = scopeState.getLeftValue();
		} else {

			leftValue = wrappedState.getLeftValue();
		}

		return leftValue;
	}

	@Override
	public void setLeftValue(CodeExpression leftValue) {
		if (wrapping) {
			scopeState.setLeftValue(leftValue);
		} else {

			wrappedState.setLeftValue(leftValue);
		}
	}

	@Override
	public void recordFact(CodeExpression fact) {
		if (wrapping) {
			throw new UnsupportedOperationException("not yet implemented");
		} else {

			wrappedState.recordFact(fact);
		}

	}

	@Override
	public void retreatFact(CodeExpression fact) {
		if (wrapping) {
			throw new UnsupportedOperationException("not yet implemented");
		} else {

			wrappedState.retreatFact(fact);
		}
	}

	public CodeState getScopeState() {
		return scopeState;
	}

	@Override
	public Set<String> variableNames() {
		Set<String> variableNames;
		if (wrapping) {
			variableNames = new HashSet<>();
			variableNames.addAll(scopeState.variableNames());
			variableNames.addAll(wrappedState.variableNames());
		} else {
			variableNames = wrappedState.variableNames();
		}
		return variableNames;

	}

	@Override
	public void undefineVariable(String variableName) {
		if (wrapping) {
			if (scopeState.isVariableDefined(variableName)) {
				scopeState.undefineVariable(variableName);
			} else {
				throw new IllegalStateException("Shouldn't happen, otherwise document why");
			}
		} else {
			wrappedState.undefineVariable(variableName);
		}
	}

	@Override
	public CodeExpression getReturnExpression() {
		return wrappedState.getReturnExpression();
	}

	@Override
	public void setReturnExpression(CodeExpression returnExpression) {
		wrappedState.setReturnExpression(returnExpression);
	}

	@Override
	public BooleanExpression getBreakCondition() {
		return wrappedState.getBreakCondition();
	}

	@Override
	public BooleanExpression getContinueCondition() {
		return wrappedState.getContinueCondition();
	}

	@Override
	public void setBreakCondition(BooleanExpression breakCondition) {
		wrappedState.setBreakCondition(breakCondition);
	}

	@Override
	public void setContinueCondition(BooleanExpression continueCondition) {
		wrappedState.setContinueCondition(continueCondition);
	}

	@Override
	public void defineFunction(FunctionDefinition function) {
		if (wrapping) {
			scopeState.defineFunction(function);
		} else {
			wrappedState.defineFunction(function);
		}
	}

	@Override
	public boolean isFunctionDefined(FunctionSignature signature) {
		return (scopeState.isFunctionDefined(signature) && wrapping) || wrappedState.isFunctionDefined(signature);
	}

	@Override
	public FunctionDefinition resolveFunction(FunctionSignature signature) {
		if (scopeState.isFunctionDefined(signature) && wrapping) {
			return scopeState.resolveFunction(signature);
		} else {
			return wrappedState.resolveFunction(signature);
		}
	}

	@Override
	public void defineClass(ClassType classType) {
		if (wrapping) {

			// when scoping, defining only locally
			scopeState.defineClass(classType);
		} else {

			wrappedState.defineClass(classType);
		}
	}

	@Override
	public ClassType resolveClass(String className) {
		// TODO Auto-generated method stub
		// return null;
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public VariableDefinition resolveVariable(String variableName) {
		VariableDefinition variableDefinition;
		if (wrapping && scopeState.isVariableDefined(variableName)) {

			// when scoping, existing scoped variables have precedence over
			// outer variables
			variableDefinition = scopeState.resolveVariable(variableName);
		} else {

			variableDefinition = wrappedState.resolveVariable(variableName);
		}
		return variableDefinition;
	}

	@Override
	public BooleanExpression getRecursionCondition(FunctionSignature signature) {
		// No scoping for recursion
		return wrappedState.getRecursionCondition(signature);
	}

	@Override
	public void setRecursionCondition(FunctionSignature signature, BooleanExpression expression) {
		// No scoping for recursion
		wrappedState.setRecursionCondition(signature, expression);
	}

	@Override
	public CodeExpression recursionCall(String functionName, CodeExpression[] parameterValues) {
		// No scoping for function call (but what about parameter values ?)
		return wrappedState.recursionCall(functionName, parameterValues);
	}

}