package net.sf.metacad.revenge.expression;

public interface PlaceholderExpression extends CodeExpression, SymbolicExpression {

	PlaceholderReference reference();

	public abstract CodeExpression getValue();

}