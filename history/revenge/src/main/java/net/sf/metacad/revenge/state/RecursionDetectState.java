package net.sf.metacad.revenge.state;

import java.util.Arrays;
import java.util.UUID;

import net.sf.metacad.revenge.definition.FunctionDefinition;
import net.sf.metacad.revenge.definition.FunctionSignature;
import net.sf.metacad.revenge.definition.RecursiveFunctionDefinition;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.FunctionCall;
import net.sf.metacad.revenge.expression.RecursiveCallExpression;

import org.apache.commons.lang.StringUtils;
import org.apache.commons.lang.builder.ToStringBuilder;

public class RecursionDetectState extends StateFilter {
	private static final long serialVersionUID = 726901380392429094L;
	private final FunctionSignature signature;
	private boolean isDetecting = true;
	private boolean recursionDetected = false;
	private final FunctionDefinition recursiveFunctionDefinition;

	public RecursionDetectState(CodeState outerState, FunctionSignature signature) {
		super(outerState);
		this.signature = signature;
		FunctionDefinition definition = wrappedState.resolveFunction(signature);
		recursiveFunctionDefinition = new RecursiveFunctionDefinition(signature.functionName, null,
				definition.parameterDefinitions, definition.returnType);
	}

	public boolean isDetecting() {
		return isDetecting;
	}

	public void setDetecting(boolean isDetecting) {
		this.isDetecting = isDetecting;
	}

	@Override
	public FunctionDefinition resolveFunction(FunctionSignature signature) {
		if (isDetecting && this.signature.equals(signature)) {

			// Avoid that the recursive function is evaluated again, and again,
			// and again...
			recursionDetected = true;
			return recursiveFunctionDefinition;
		} else {
			return wrappedState.resolveFunction(signature);
		}
	}

	public boolean isRecursionDetected() {
		return recursionDetected;
	}

	@Override
	public CodeExpression recursionCall(String functionName, CodeExpression[] parameterValues) {
		FunctionCall.signature(functionName, Arrays.asList(parameterValues));
		if (isDetecting && signature.equals(signature)) {
			FunctionDefinition definition = wrappedState.resolveFunction(signature);
			// This should never be used, but must return something...
			// Probably should merge RecursionDetect and RecursionRecord
			String placeholderName = functionName + "_"
					+ StringUtils.replaceChars(UUID.randomUUID().toString(), '-', '_');
			RecursiveCallExpression fcp = new RecursiveCallExpression(placeholderName, placeholderName, functionName,
					Arrays.asList(parameterValues), definition,
					new ToStringBuilder(this).append(creatorDescription).toString());
			return fcp;
		} else {
			return wrappedState.recursionCall(functionName, parameterValues);
		}
	}

}
