package net.sf.metacad.revenge.state;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import net.sf.metacad.revenge.definition.FunctionSignature;
import net.sf.metacad.revenge.expression.logic.BooleanValueExpression;
import net.sf.metacad.revenge.type.NumericType;

import org.junit.Test;

import bsh.JavaParser;

public class StandaloneStateBaseTest {

	@Test
	public void testFunctionDefinition() throws Exception {
		ProgramState state = new ProgramState();
		FunctionSignature fooSignature = new FunctionSignature("foo");
		assertFalse(state.isFunctionDefined(fooSignature));
		CodeState stateModified = JavaParser.evaluate("int foo() {return 7;}; foo();", state);
		assertTrue(stateModified.isFunctionDefined(fooSignature));
		assertEquals(fooSignature, state.resolveFunction(fooSignature).signature());
	}

	@Test
	public void testRecursiveConditionWithArgument() throws Exception {
		ProgramState state = new ProgramState();
		FunctionSignature fooSignature = new FunctionSignature("foo", NumericType.INT);
		assertFalse(state.isFunctionDefined(fooSignature));
		assertEquals(BooleanValueExpression.FALSE, state.getRecursionCondition(fooSignature));
		CodeState stateModified = JavaParser.evaluate("int foo(int a) {return a;};", state);
		assertTrue(stateModified.isFunctionDefined(fooSignature));
		assertEquals(fooSignature, state.resolveFunction(fooSignature).signature());
	}
}
