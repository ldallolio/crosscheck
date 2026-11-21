package net.sf.metacad.revenge.expression;

public interface SymbolicExpression extends CodeExpression, UnaryExpression {

	String getLocalName();

	String getName();

}