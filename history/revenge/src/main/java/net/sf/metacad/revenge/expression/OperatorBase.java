package net.sf.metacad.revenge.expression;

import java.io.Serializable;

import org.apache.commons.lang.SerializationUtils;

public abstract class OperatorBase implements Operator, Cloneable, Serializable {

	private static final long serialVersionUID = 5764213928829920543L;

	@Override
	protected Object clone() throws CloneNotSupportedException {
		return SerializationUtils.clone(this);
	}

	@Override
	public Operator cloneOperator() {
		try {
			return (Operator) this.clone();
		} catch (CloneNotSupportedException e) {
			throw new IllegalStateException(e);
		}
	}
}
