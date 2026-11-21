package net.sf.metacad.revenge.expression;

import java.io.Serializable;

public interface Operator extends Cloneable, Serializable {
	Operator cloneOperator();
}
