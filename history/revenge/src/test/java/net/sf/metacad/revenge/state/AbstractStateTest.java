package net.sf.metacad.revenge.state;

import static org.junit.Assert.assertEquals;
import net.sf.metacad.revenge.expression.MetaExpression;
import net.sf.metacad.revenge.expression.MultipleValueExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;

import org.junit.Test;

import bsh.JavaParser;

public class AbstractStateTest {

	@Test
	public void testClone1() throws Exception {
		ProgramState toBeCloned = new ProgramState();
		CodeState stateModified = JavaParser.evaluate("int i = 7;", toBeCloned.cloneState());
		assertEquals(MetaExpression.NOT_DEFINED_VARIABLE, toBeCloned.variableValue("i"));
		assertEquals(7, ((IntegerValueExpression) stateModified.variableValue("i")).value);
	}

	@Test
	public void testClone2() throws Exception {
		CodeState initialState = JavaParser.evaluate("int i = 7;", new ProgramState());
		PlaceholderState placeholderState = new PlaceholderState(initialState);
		assertEquals(7, ((IntegerValueExpression) initialState.variableValue("i")).value);
		MultipleValueExpression multipleExpr = (MultipleValueExpression) placeholderState.variableValue("i");
		assertEquals(1, multipleExpr.getValues().size());
		CodeState clonedState = placeholderState.cloneState();
		clonedState.assignVariable("i", new IntegerValueExpression(8));
		assertEquals(1, multipleExpr.getValues().size());
	}

}
