package net.sf.metacad.revenge.definition;

import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.MetaExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;
import net.sf.metacad.revenge.type.NumericType;

import org.apache.commons.lang.builder.ToStringBuilder;

/**
 * Only the variable definition, not the current value
 * 
 * @author user
 * 
 */
public class VariableDefinition implements CodeDefinition {

	private static final long serialVersionUID = 3197479448600944577L;
	public final String name;
	public final CodeType type;
	public final CodeExpression initialValue;

	public VariableDefinition(String variableName, CodeType variableType, CodeExpression variableInitialValue) {
		this.name = variableName;
		this.type = variableType;
		if (variableInitialValue != null) {
			this.initialValue = variableInitialValue;
		} else {
			this.initialValue = MetaExpression.DEFINED_BUT_NOT_INITIALIZED_VARIABLE;
		}
	}

	/**
	 * For non declarative languages type variables might be inferred
	 * 
	 * @param variableName
	 * @param variableInitialValue
	 */
	public VariableDefinition(String variableName, CodeExpression variableInitialValue) {
		this.name = variableName;
		this.type = variableInitialValue.type();
		this.initialValue = variableInitialValue;
	}

	public VariableDefinition(String variableName, CodeType variableType) {
		this.name = variableName;
		this.type = variableType;
		// TODO handle initial implicit value for float primitive
		// variables
		if (NumericType.INT.equals(variableType)) {
			this.initialValue = new IntegerValueExpression(0);
		} else {
			this.initialValue = MetaExpression.NULL_EXPRESSION;
		}
	}

	@Override
	public String toString() {
		return ToStringBuilder.reflectionToString(this);
	}

	public CodeState evaluate(CodeState initialState) {
		initialState.defineVariable(this);
		initialState.setLeftValue(this.initialValue);
		return initialState;
	}
}
