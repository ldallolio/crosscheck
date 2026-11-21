package net.sf.metacad.revenge.expression;

import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;

import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;

public class PlaceholderReference extends VariableReference {

	private static final long serialVersionUID = 5048445848099294697L;
	public final String placeholderName;
	public final String placeholderLocalName;
	public final String variableName;
	public CodeExpression value;
	protected String creatorDescription;

	public PlaceholderReference(String placeholderName, String placeholderLocalName, String variableName,
			CodeExpression variableCurrentValue, String creatorDescription) {
		super(placeholderName, placeholderLocalName, variableCurrentValue.type());
		this.placeholderName = placeholderName;
		this.variableName = variableName;
		this.placeholderLocalName = placeholderLocalName;
		value = variableCurrentValue;
		this.creatorDescription = creatorDescription;
	}

	@Override
	public boolean isAbout(String variableName) {
		return value.isAbout(variableName);
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		TreeSet<VariableReference> treeSet = new TreeSet<>();
		treeSet.add(this);
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
		CodeExpression placeholderValue = initialState.variableValue(placeholderName);
		initialState.setLeftValue(placeholderValue);
		return initialState;
	}

	@Override
	public String toString() {
		return placeholderLocalName + "_ref";
	}

}