package net.sf.metacad.revenge.state;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.UUID;

import net.sf.metacad.revenge.definition.FunctionDefinition;
import net.sf.metacad.revenge.definition.FunctionSignature;
import net.sf.metacad.revenge.definition.RecursiveFunctionDefinition;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.FunctionCall;
import net.sf.metacad.revenge.expression.RecursiveCallExpression;

import org.apache.commons.lang.StringUtils;
import org.apache.commons.lang.builder.ToStringBuilder;

public class RecursionRecordState extends StateFilter {
	private static final long serialVersionUID = 3388070470670099342L;
	private final FunctionSignature signature;

	public FunctionSignature getSignature() {
		return signature;
	}

	private final RecursiveFunctionDefinition recursiveFunctionDefinition;
	public final Map<String, RecursiveCallExpression> functionPlaceholderByName = new LinkedHashMap<>();
	private boolean isRecording = true;
	public static int globalCounter = 0;

	public RecursionRecordState(CodeState outerState, FunctionSignature signature) {
		super(outerState);
		this.signature = signature;
		FunctionDefinition definition = wrappedState.resolveFunction(signature);
		recursiveFunctionDefinition = new RecursiveFunctionDefinition(signature.functionName, null,
				definition.parameterDefinitions, definition.returnType);
	}

	@Override
	public FunctionDefinition resolveFunction(FunctionSignature signature) {
		if (isRecording && this.signature.equals(signature)) {

			// Avoid that the recursive function is evaluated again, and again,
			// and again...
			return recursiveFunctionDefinition;
		} else {
			return wrappedState.resolveFunction(signature);
		}
	}

	public boolean isRecording() {
		return isRecording;
	}

	public void stopRecording() {
		isRecording = false;
	}

	public RecursiveFunctionDefinition getRecursiveFunctionDefinition() {
		return recursiveFunctionDefinition;
	}

	@Override
	public CodeExpression recursionCall(String functionName, CodeExpression[] parameterValues) {
		FunctionSignature signature = FunctionCall.signature(functionName, Arrays.asList(parameterValues));
		if (isRecording) {
			if (this.signature.equals(signature)) {
				FunctionDefinition definition = wrappedState.resolveFunction(signature);

				String placeholderLocalName = functionName + "()_" + globalCounter++;
				String placeholderName = placeholderLocalName + "_"
						+ StringUtils.replaceChars(UUID.randomUUID().toString(), '-', '_');
				RecursiveCallExpression fcp = new RecursiveCallExpression(placeholderName, placeholderLocalName,
						functionName, Arrays.asList(parameterValues), definition,
						new ToStringBuilder(this).append(creatorDescription).toString());
				functionPlaceholderByName.put(placeholderName, fcp);
				return fcp;
			} else if (functionPlaceholderByName.containsKey(functionName)) {
				return functionPlaceholderByName.get(functionName);
			} else {
				return wrappedState.recursionCall(functionName, parameterValues);
			}
		} else {
			return wrappedState.recursionCall(functionName, parameterValues);
		}
	}

}
