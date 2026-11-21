package net.sf.metacad.revenge.state;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.UUID;
import java.util.concurrent.atomic.AtomicInteger;

import net.sf.metacad.revenge.definition.VariableDefinition;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.MultipleConditionedExpression;
import net.sf.metacad.revenge.expression.MultipleValueExpression;
import net.sf.metacad.revenge.expression.MultipleValuePlaceholder;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerPlaceholder;

import org.apache.commons.lang.StringUtils;
import org.apache.commons.lang.builder.ToStringBuilder;

/**
 * 
 * State adapter for handling variables in a while loop or in a recursive function call, hiding original state to the
 * cycle statements by returning placeholders value instead of actual variable values so that, when cycle cardinality
 * will be known, real variable value will be calculated.
 * 
 * Example : int i = 0; while(...) i++; here "++ increment" must not see the real value of i (at the first iteration)
 * until we know how many iterations whill happen
 * 
 * This is a not simply a scoped state, since multiple placeholders may be issued and remembered for the same variable.
 * 
 * Example : int i = x = y = 0; while(i < 5) {i++;x = i;i++;y = i}
 * 
 * Also, even outer variables that have not been changed (yet) must be placeholded because later in the cycle they could
 * change, so in the next iteration their value could be different
 * 
 * Example : int x = 0; int y = 7; while(...) {x = y;y++;}
 * 
 * Note that other inner scoping could be dropping its out-of-scope variables, but since they are "mute variables", they
 * disappear from expressions so they should not need to be "placeholded". Also note that other inner scoping cannot be
 * "placeholded" in any way, think about :
 * 
 * while(...) { int x = 0; if (...) {int y = 0;} ...}
 * 
 * In this example, the while loop can "know" about "x", but there is no way that it could "know" about "y".
 * 
 * @author Luca Dall'Olio
 * 
 */
public final class PlaceholderState extends ScopedStateBase {

	private static final long serialVersionUID = 8220416979669456835L;

	private boolean placeholding = true;

	private final Map<String, String> variableNameByPlaceholderName = new LinkedHashMap<>();
	private Map<String, CodeExpression> placeholderFinalValuesByName = new LinkedHashMap<>();
	private static Map<String, AtomicInteger> globalCounterByVariableName = new LinkedHashMap<>();

	/**
	 * When I study an evaluated cycle, I must stop placeholder generation (in other terms, I must "lie" to any "while
	 * inner statement" but not to the "while-statement" itself).
	 * 
	 * This is in fact a "virtual state", since I must keep track of placeholders without altering original state.
	 * 
	 */
	public PlaceholderState(CodeState originalState) {
		super(originalState);
	}

	@Override
	public CodeExpression variableValue(String variableName) {

		CodeExpression variableValue = null;

		if (placeholding) {

			if (variableNameByPlaceholderName.containsKey(variableName)) {
				String placeholderName = variableName;
				String originalVariableName = variableNameByPlaceholderName.get(placeholderName);
				MultipleValueExpression multipleValue = (MultipleValueExpression) super.variableValue(
						originalVariableName);
				variableValue = multipleValue.getCurrentValue();
			} else {
				if (!super.isLocallyDefined(variableName)) {
					int globalCounter = 0;
					if (globalCounterByVariableName.containsKey(variableName)) {
						globalCounter = globalCounterByVariableName.get(variableName).incrementAndGet();
					} else {
						globalCounterByVariableName.put(variableName, new AtomicInteger(0));
					}
					// TODO : handle better naming : it would be useful if
					// placeholders could be distinguished by variables simply
					// by
					// name,
					// should probably use a namespace prefix such as : "ph://"
					String placeholderLocalName = variableName + "_" + globalCounter;
					String placeholderName = placeholderLocalName + "_"
							+ StringUtils.replaceChars(UUID.randomUUID().toString(), '-', '_');
					CodeExpression placeholder = createPlaceholder(placeholderName, placeholderLocalName, variableName,
							super.variableValue(variableName));
					variableValue = new MultipleValueExpression(placeholder);
					VariableDefinition variableDefinition = new VariableDefinition(variableName, variableValue.type(),
							variableValue);
					super.defineVariable(variableDefinition);
					variableNameByPlaceholderName.put(placeholderName, variableName);
				} else {
					MultipleValueExpression multipleValue = (MultipleValueExpression) super.variableValue(variableName);
					variableValue = multipleValue.getCurrentValue();
				}
			}

		} else {
			if (variableNameByPlaceholderName.containsKey(variableName)) {
				variableValue = placeholderFinalValuesByName.get(variableName);
			} else {
				variableValue = super.variableValue(variableName);
			}
		}

		return variableValue;
	}

	@Override
	public void assignVariable(String variableName, CodeExpression newValue) {

		// define placeholders only for existing outer codeVariables
		if (!super.isVariableDefined(variableName)) {
			throw new IllegalArgumentException(
					"CodeVariable : [" + variableName + "] cannot be initialized since it is not defined.");
		}

		if (placeholding) {
			// lazily define a virtual value
			// This is different from a scoped state, just think of this
			// example:
			//
			// int i = 0; while(...) i++;
			//
			// in this case there would be no need to define a scoped variable
			// for i, but I have to protect the original, initial value from the
			// assignment
			if (!super.isLocallyDefined(variableName)) {
				int globalCounter = 0;
				if (globalCounterByVariableName.containsKey(variableName)) {
					globalCounter = globalCounterByVariableName.get(variableName).incrementAndGet();
				} else {
					globalCounterByVariableName.put(variableName, new AtomicInteger(0));
				}
				String placeholderLocalName = variableName + "_" + globalCounter;
				String placeholderName = placeholderLocalName + "_"
						+ StringUtils.replaceChars(UUID.randomUUID().toString(), '-', '_');
				CodeExpression placeholder = createPlaceholder(placeholderName, placeholderLocalName, variableName,
						newValue);
				MultipleValueExpression placeholderVariableValue = new MultipleValueExpression(placeholder);
				VariableDefinition placeholderVariableDefinition = new VariableDefinition(variableName,
						placeholderVariableValue.type(), placeholderVariableValue);
				super.defineVariable(placeholderVariableDefinition);
				variableNameByPlaceholderName.put(placeholderName, variableName);
			} else {
				int globalCounter = 0;
				if (globalCounterByVariableName.containsKey(variableName)) {
					globalCounter = globalCounterByVariableName.get(variableName).get();
				} else {
					globalCounterByVariableName.put(variableName, new AtomicInteger(0));
				}
				MultipleValueExpression multipleValue = (MultipleValueExpression) super.variableValue(variableName);
				String placeholderLocalName;
				if (globalCounter >= 1) {
					placeholderLocalName = variableName + "_" + globalCounter + "_" + multipleValue.getValues().size();
				} else {
					placeholderLocalName = variableName + "_" + multipleValue.getValues().size();
				}

				String placeholderName = placeholderLocalName + "_"
						+ StringUtils.replaceChars(UUID.randomUUID().toString(), '-', '_');
				CodeExpression placeholder = createPlaceholder(placeholderName, placeholderLocalName, variableName,
						newValue);
				multipleValue.addValue(placeholder);
				variableNameByPlaceholderName.put(placeholderName, variableName);
			}

		} else {
			// when not placeholding, just pass it through
			super.assignVariable(variableName, newValue);
		}

	}

	private CodeExpression createPlaceholder(String placeholderName, String placeholderLocalName, String variableName,
			CodeExpression newValue) {
		CodeExpression placeholder;
		if (newValue instanceof IntegerExpression) {
			placeholder = new IntegerPlaceholder(placeholderName, placeholderLocalName, variableName, newValue,
					new ToStringBuilder(this).append(creatorDescription).toString());
		} else if (newValue instanceof MultipleValueExpression) {
			placeholder = new MultipleValuePlaceholder(placeholderName, placeholderLocalName, variableName, newValue,
					new ToStringBuilder(this).append(creatorDescription).toString());
		} else if (newValue instanceof MultipleConditionedExpression) {
			placeholder = new MultipleValuePlaceholder(placeholderName, placeholderLocalName, variableName, newValue,
					new ToStringBuilder(this).append(creatorDescription).toString());
		} else {
			throw new UnsupportedOperationException("Placeholder for type : [" + newValue.type() + "] not yet handled");
		}
		return placeholder;
	}

	@Override
	public void defineVariable(VariableDefinition variable) {
		// You can define variables in the while clause, or after while has
		// closed :
		// while((int i = 0) <= 7) i++;
		// while(...) {...}; int i = 0;
		super.defineVariable(variable);
	}

	public void setPlaceholding(boolean placeholding) {
		this.placeholding = placeholding;
	}

	public boolean isPlaceholding() {
		return placeholding;
	}

	public String resolvePlaceholder(String placeholderName) {
		return variableNameByPlaceholderName.get(placeholderName);
	}

	public Map<String, CodeExpression> getPlaceholderFinalValues() {
		return placeholderFinalValuesByName;
	}

	public void setPlaceholderFinalValues(Map<String, CodeExpression> placeholderFinalValues) {
		placeholderFinalValuesByName = placeholderFinalValues;
	}

	@Override
	public CodeExpression recursionCall(String functionName, CodeExpression[] parameterValues) {
		// TODO Auto-generated method stub
		// return null;
		throw new UnsupportedOperationException("not yet implemented");
	}

}