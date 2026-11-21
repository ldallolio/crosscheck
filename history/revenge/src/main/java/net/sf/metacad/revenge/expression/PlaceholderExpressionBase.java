package net.sf.metacad.revenge.expression;

import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;

import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;

public abstract class PlaceholderExpressionBase extends ExpressionBase
		implements UnaryExpression, PlaceholderExpression {

	private static final long serialVersionUID = 3447348473942289118L;
	public final String name;
	public final String localName;
	public final String variableName;
	public final CodeExpression value;
	protected String creatorDescription;

	public PlaceholderExpressionBase(String placeholderName, String placeholderLocalName, String variableName,
			CodeExpression variableCurrentValue, String creatorDescription) {
		name = placeholderName;
		this.variableName = variableName;
		localName = placeholderLocalName;
		value = variableCurrentValue;
		this.creatorDescription = creatorDescription;
	}

	public PlaceholderExpressionBase(String placeholderName) {
		name = placeholderName;
		variableName = placeholderName;
		localName = placeholderName;
		value = null;
		creatorDescription = "";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see net.sf.metacad.revenge.expression.PlaceholderExpression#reference()
	 */
	@Override
	public PlaceholderReference reference() {
		return new PlaceholderReference(name, localName, variableName, value, creatorDescription);
	}

	@Override
	public boolean isAbout(String variableName) {
		return value.isAbout(variableName);
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		TreeSet<VariableReference> treeSet = new TreeSet<>();
		// should be treated like a constant
		return treeSet;
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		visitor.useVariable(this);
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		// Example : for (i = 1:3) x = y
		// becomes x = y
		visitor.useVariable(this);
	}

	@Override
	public CodeType type() {
		return value.type();
	}

	@Override
	public CodeState evaluate(CodeState initialState) {
		// A placeholder must avoid to show inner variables even during
		// evaluation
		CodeExpression placeholderValue = initialState.variableValue(name);
		initialState.setLeftValue(placeholderValue);
		return initialState;
	}

	@Override
	public final String getName() {
		return name;
	}

	@Override
	public final String getLocalName() {
		return localName;
	}

	@Override
	public String toString() {
		return localName;
	}

	@Override
	public final CodeExpression getValue() {
		return value;
	}

}