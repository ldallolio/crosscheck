package net.sf.metacad.revenge.state;

import java.io.Serializable;

import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.type.CodeType;

import org.apache.commons.lang.builder.ToStringBuilder;

/**
 * Implements a variable, with its current value
 * 
 * @author user
 * 
 */
class CodeVariable implements Cloneable, Serializable {

	private static final long serialVersionUID = -1594853268588027962L;
	String name;
	CodeExpression value;
	CodeType type;

	CodeVariable(String name, CodeExpression value, CodeType type) {
		super();
		this.name = name;
		this.value = value;
		this.type = type;
	}

	String getName() {
		return name;
	}

	void setName(String name) {
		this.name = name;
	}

	CodeExpression getValue() {
		return value;
	}

	void setValue(CodeExpression value) {
		this.value = value;
	}

	@Override
	public String toString() {
		return new ToStringBuilder(this).append("name", this.name).append("value", this.value).toString();
	}

	CodeType getType() {
		return type;
	}

}
