package net.sf.metacad.revenge.state;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import net.sf.metacad.revenge.definition.FunctionDefinition;
import net.sf.metacad.revenge.definition.FunctionSignature;
import net.sf.metacad.revenge.definition.VariableDefinition;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.MetaExpression;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.BooleanValueExpression;
import net.sf.metacad.revenge.type.ClassType;

/**
 * Base class for most state implementation
 * 
 * Records variables using a map
 * 
 * @author ld
 */
abstract class StandaloneStateBase extends AbstractState {

	private static final long serialVersionUID = -1198293770785001439L;
	protected Map<String, CodeVariable> codeVariables = new LinkedHashMap<>();
	protected List<CodeExpression> facts = new Vector<>();
	protected Map<FunctionSignature, FunctionDefinition> functionDefinitions = new LinkedHashMap<>();
	protected Map<FunctionSignature, BooleanExpression> recursionConditions = new LinkedHashMap<>();
	protected Map<String, ClassType> classTypes = new LinkedHashMap<>();
	protected CodeExpression leftValue = MetaExpression.NO_LEFT_VALUE;
	protected CodeExpression returnExpression = MetaExpression.NO_RETURN_VALUE;
	protected BooleanExpression returnCondition = BooleanValueExpression.FALSE;
	protected BooleanExpression breakCondition = BooleanValueExpression.FALSE;
	protected BooleanExpression continueCondition = BooleanValueExpression.FALSE;

	@Override
	public BooleanExpression getBreakCondition() {
		return breakCondition;
	}

	@Override
	public void setBreakCondition(BooleanExpression breakCondition) {
		this.breakCondition = breakCondition;
	}

	@Override
	public BooleanExpression getContinueCondition() {
		return continueCondition;
	}

	@Override
	public void setContinueCondition(BooleanExpression continueCondition) {
		this.continueCondition = continueCondition;
	}

	@Override
	public CodeExpression getReturnExpression() {
		return returnExpression;
	}

	@Override
	public void setReturnExpression(CodeExpression returnExpression) {
		this.returnExpression = returnExpression;
	}

	@Override
	public CodeExpression variableValue(String variableName) {

		if (codeVariables.containsKey(variableName)) {
			return codeVariables.get(variableName).getValue();
		} else {

			// instead of throwing exception, I return a special variable, so it
			// is easier to assert things in test, also passing-through
			// algorithms should be more tolerant about out-of-scope variables
			return MetaExpression.NOT_DEFINED_VARIABLE;
		}

	}

	@Override
	public boolean isVariableDefined(String variableName) {
		return codeVariables.containsKey(variableName);
	}

	@Override
	public void assignVariable(String variableName, CodeExpression newValue) {
		if (codeVariables.containsKey(variableName)) {
			codeVariables.get(variableName).setValue(newValue);
		} else {
			throw new IllegalArgumentException("Cannot assign undefined variable : [" + variableName + "]");
		}
	}

	@Override
	public void recordFact(CodeExpression fact) {
		facts.add(fact);
	}

	@Override
	public void retreatFact(CodeExpression fact) {
		// TODO define equals!
		facts.remove(fact);
	}

	@Override
	public void defineVariable(VariableDefinition variableDefinition) {
		if (isVariableDefined(variableDefinition.name)) {
			throw new IllegalArgumentException("Cannot define already defined variable : [" + variableDefinition + "]");
		} else {
			codeVariables.put(variableDefinition.name, new CodeVariable(variableDefinition.name,
					variableDefinition.initialValue, variableDefinition.type));
		}
	}

	public void putAllVariables(Map<String, CodeVariable> variables) {
		for (String variableName : variables.keySet()) {
			// Not assigning map directly so also facts, variable overwritings,
			// etc. will be somehow handled
			CodeVariable codeVariable = variables.get(variableName);
			VariableDefinition variableDefinition = new VariableDefinition(variableName, codeVariable.getType(),
					codeVariable.getValue());
			defineVariable(variableDefinition);
		}
	}

	@Override
	public CodeExpression getLeftValue() {
		return leftValue;
	}

	@Override
	public void setLeftValue(CodeExpression leftValue) {
		this.leftValue = leftValue;
	}

	@Override
	public Set<String> variableNames() {
		return codeVariables.keySet();
	}

	@Override
	public void undefineVariable(String variableName) {
		if (!isVariableDefined(variableName)) {
			throw new IllegalArgumentException(
					"Cannot undefine a not already defined variable : [" + variableName + "]");
		} else {

			// TODO gestire i tipi
			codeVariables.remove(variableName);
			for (CodeExpression fact : facts) {
				if (fact.isAbout(variableName)) {
					retreatFact(fact);
				}
			}
		}

	}

	@Override
	public void defineFunction(FunctionDefinition function) {
		functionDefinitions.put(function.signature(), function);
	}

	@Override
	public FunctionDefinition resolveFunction(FunctionSignature signature) {
		if (!functionDefinitions.containsKey(signature)) {
			throw new IllegalArgumentException("Function : [" + signature + "] is not defined");
		}

		FunctionDefinition functionDefinition = functionDefinitions.get(signature);
		return functionDefinition;
	}

	@Override
	public boolean isFunctionDefined(FunctionSignature signature) {
		return functionDefinitions.containsKey(signature);
	}

	@Override
	public ClassType resolveClass(String className) {
		return classTypes.get(className);
	}

	@Override
	public void defineClass(ClassType classType) {
		classTypes.put(classType.getClassName(), classType);
	}

	@Override
	public VariableDefinition resolveVariable(String variableName) {
		CodeVariable codeVariable = codeVariables.get(variableName);
		if (codeVariable == null) {
			throw new IllegalArgumentException("Variable : [" + variableName + "] is not defined. Defined variables : ["
					+ codeVariables.keySet() + "]");
		}
		return new VariableDefinition(variableName, codeVariable.type);
	}

	@Override
	public BooleanExpression getRecursionCondition(FunctionSignature signature) {
		if (recursionConditions.containsKey(signature)) {
			return recursionConditions.get(signature);
		} else {
			return BooleanValueExpression.FALSE;
		}
	}

	@Override
	public void setRecursionCondition(FunctionSignature signature, BooleanExpression expression) {
		recursionConditions.put(signature, expression);
	}

}