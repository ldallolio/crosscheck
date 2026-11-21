package net.sf.metacad.revenge.state;

import java.util.Set;

import net.sf.metacad.revenge.definition.VariableDefinition;
import net.sf.metacad.revenge.expression.CodeExpression;

interface VariableCodeState {

	public abstract boolean isVariableDefined(String variableName);

	public abstract void defineVariable(VariableDefinition variable);

	public abstract VariableDefinition resolveVariable(String variableName);

	public abstract void assignVariable(String variableName, CodeExpression newValue);

	public abstract void undefineVariable(String variableName);

	public abstract CodeExpression variableValue(String variableName);

	public abstract Set<String> variableNames();

}