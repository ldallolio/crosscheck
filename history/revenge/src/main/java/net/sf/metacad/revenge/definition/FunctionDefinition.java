package net.sf.metacad.revenge.definition;

import java.util.List;
import java.util.Vector;

import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.StateTransition;
import net.sf.metacad.revenge.statement.Block;
import net.sf.metacad.revenge.type.CodeType;

import org.apache.commons.lang.builder.EqualsBuilder;
import org.apache.commons.lang.builder.HashCodeBuilder;
import org.apache.commons.lang.builder.ToStringBuilder;

public class FunctionDefinition implements CodeDefinition {

	private static final long serialVersionUID = 5758411027681272555L;

	public final String functionName;

	public final StateTransition functionBody;

	public final List<VariableDefinition> parameterDefinitions;

	public final CodeType returnType;

	public FunctionDefinition(String functionName, Block functionBody, List<VariableDefinition> parameters,
			CodeType returnType) {
		this.functionName = functionName;
		this.functionBody = functionBody;
		parameterDefinitions = parameters;
		this.returnType = returnType;
	}

	public FunctionSignature signature() {
		List<CodeType> parameterTypes = new Vector<>();
		for (VariableDefinition parameterDefinition : parameterDefinitions) {
			parameterTypes.add(parameterDefinition.type);
		}
		return new FunctionSignature(functionName, parameterTypes);
	}

	@Override
	public CodeState evaluate(CodeState initialState) {
		initialState.defineFunction(this);
		return initialState;
	}

	@Override
	public boolean equals(Object obj) {
		return EqualsBuilder.reflectionEquals(this, obj);
	}

	@Override
	public int hashCode() {
		return HashCodeBuilder.reflectionHashCode(this);
	}

	@Override
	public String toString() {
		return ToStringBuilder.reflectionToString(this);
	}

}