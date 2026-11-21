package net.sf.metacad.revenge.state;

import java.util.Set;

import net.sf.metacad.revenge.definition.FunctionDefinition;
import net.sf.metacad.revenge.definition.FunctionSignature;
import net.sf.metacad.revenge.definition.VariableDefinition;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.type.ClassType;

abstract class StateFilter extends WrappingStateBase {

	private static final long serialVersionUID = -924077945245896443L;

	public StateFilter(CodeState wrappedState) {
		super(wrappedState);
	}

	@Override
	public void assignVariable(String variableName, CodeExpression newValue) {
		wrappedState.assignVariable(variableName, newValue);
	}

	@Override
	public void defineClass(ClassType classType) {
		wrappedState.defineClass(classType);
	}

	@Override
	public void defineFunction(FunctionDefinition function) {
		wrappedState.defineFunction(function);
	}

	@Override
	public void defineVariable(VariableDefinition variable) {
		wrappedState.defineVariable(variable);
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
	public CodeExpression getLeftValue() {
		return wrappedState.getLeftValue();
	}

	@Override
	public BooleanExpression getRecursionCondition(FunctionSignature signature) {
		return wrappedState.getRecursionCondition(signature);
	}

	@Override
	public CodeExpression getReturnExpression() {
		return wrappedState.getReturnExpression();
	}

	@Override
	public boolean isFunctionDefined(FunctionSignature signature) {
		return wrappedState.isFunctionDefined(signature);
	}

	@Override
	public boolean isVariableDefined(String variableName) {
		return wrappedState.isVariableDefined(variableName);
	}

	@Override
	public void recordFact(CodeExpression fact) {
		wrappedState.recordFact(fact);
	}

	@Override
	public ClassType resolveClass(String className) {
		return wrappedState.resolveClass(className);
	}

	@Override
	public FunctionDefinition resolveFunction(FunctionSignature signature) {
		return wrappedState.resolveFunction(signature);
	}

	@Override
	public VariableDefinition resolveVariable(String variableName) {
		return wrappedState.resolveVariable(variableName);
	}

	@Override
	public void retreatFact(CodeExpression fact) {
		wrappedState.retreatFact(fact);
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
	public void setLeftValue(CodeExpression leftValue) {
		wrappedState.setLeftValue(leftValue);
	}

	@Override
	public void setRecursionCondition(FunctionSignature signature, BooleanExpression expression) {
		wrappedState.setRecursionCondition(signature, expression);
	}

	@Override
	public void setReturnExpression(CodeExpression returnExpression) {
		wrappedState.setReturnExpression(returnExpression);
	}

	@Override
	public void undefineVariable(String variableName) {
		wrappedState.undefineVariable(variableName);
	}

	@Override
	public Set<String> variableNames() {
		return wrappedState.variableNames();
	}

	@Override
	public CodeExpression variableValue(String variableName) {
		return wrappedState.variableValue(variableName);
	}

	@Override
	public CodeExpression recursionCall(String functionName, CodeExpression[] parameterValues) {
		return wrappedState.recursionCall(functionName, parameterValues);
	}

}
