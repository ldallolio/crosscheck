package net.sf.metacad.revenge.statement;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.state.CodeState;

import org.junit.Test;

import bsh.JavaParser;

public class AssignVariableTest {

	@Test
	public void testAssignment() throws Exception {
		CodeState finalState = JavaParser.evaluate("int var1 = 2;");
		assertNotNull(finalState);
		assertEquals(2, ((IntegerValueExpression) finalState.getLeftValue()).value);
		assertEquals(2, ((IntegerValueExpression) finalState.variableValue("var1")).value);
	}

	@Test
	public void testAssignmentPostincrement() throws Exception {
		CodeState finalState = JavaParser.evaluate("int var1 = 2; var1++;");
		assertNotNull(finalState);
		assertEquals(2, ((IntegerValueExpression) finalState.getLeftValue()).value);
		assertEquals(3, ((IntegerValueExpression) finalState.variableValue("var1")).value);
	}

	@Test
	public void testPostincrementReassign() throws Exception {
		CodeState finalState = JavaParser.evaluate("int var1 = 2; var1 = var1++;");
		assertNotNull(finalState);
		assertEquals(2, ((IntegerValueExpression) finalState.getLeftValue()).value);
		assertEquals(2, ((IntegerValueExpression) finalState.variableValue("var1")).value);
	}

}
