package net.sf.metacad.revenge.state;

import static org.junit.Assert.assertEquals;
import net.sf.metacad.revenge.definition.VariableDefinition;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.logic.BooleanValueExpression;
import net.sf.metacad.revenge.type.NumericType;

import org.junit.Test;

public class ConditionedStateTest {

	@Test
	public void testExternalVariable() {
		ProgramState programState = new ProgramState();
		programState.defineVariable(new VariableDefinition("a", NumericType.INT, new IntegerValueExpression(0)));
		ConditionedState conditionedState = new ConditionedState(BooleanValueExpression.TRUE, programState);
		// Example int a = 0;if (...) System.out.println(a);
		assertEquals(0, ((IntegerValueExpression) conditionedState.variableValue("a")).value);
		// Example int a = 0;if (...) a = 7; System.out.println(a);
		conditionedState.assignVariable("a", new IntegerValueExpression(7));
		assertEquals(7, ((IntegerValueExpression) conditionedState.variableValue("a")).value);
		// Example int a = 0;if (...) {a = 7; a = 8;} System.out.println(a);
		conditionedState.assignVariable("a", new IntegerValueExpression(8));
		assertEquals(8, ((IntegerValueExpression) conditionedState.variableValue("a")).value);
		// Example int a = 0;if (...) a = 7; ... a = 5; System.out.println(a);
		conditionedState.stopConditioning();
		conditionedState.assignVariable("a", new IntegerValueExpression(5));
		assertEquals(5, ((IntegerValueExpression) conditionedState.variableValue("a")).value);
	}

}
