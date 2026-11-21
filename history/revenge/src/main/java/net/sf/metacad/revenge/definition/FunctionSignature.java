package net.sf.metacad.revenge.definition;

import java.io.Serializable;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import net.sf.metacad.revenge.type.CodeType;

import org.apache.commons.lang.builder.EqualsBuilder;
import org.apache.commons.lang.builder.HashCodeBuilder;

public class FunctionSignature implements Serializable {

	private static final long serialVersionUID = 4169837159979699220L;
	public final String functionName;
	public final List<CodeType> parameterTypes;

	public FunctionSignature(String functionName) {
		super();
		this.functionName = functionName;
		this.parameterTypes = Collections.emptyList();
	}

	public FunctionSignature(String functionName, CodeType... codeTypes) {
		super();
		this.functionName = functionName;
		this.parameterTypes = Arrays.asList(codeTypes);
	}

	public FunctionSignature(String functionName, List<CodeType> parameterTypes) {
		super();
		this.functionName = functionName;
		this.parameterTypes = parameterTypes;
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
		return this.functionName + "(" + this.parameterTypes.toString() + ")";
	}

}
