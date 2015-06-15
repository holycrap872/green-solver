package za.ac.sun.cs.green.expr;

import java.util.Map;
import java.util.Set;
import java.util.Stack;

import za.ac.sun.cs.green.resources.IdentityHashSet;
import za.ac.sun.cs.green.service.bvfactorizer.resources.AVStack;
import za.ac.sun.cs.green.service.bvfactorizer.resources.SelectStore;
import za.ac.sun.cs.green.service.bvrenamer.VarData;

public class Alias extends Expression{
	
	final private String symbol;
	final private Expression expression;
	
	//Informs visitor whether to explore subexpression
	private boolean explore;
	
	
	private AVStack factorizerState;
	private AVStack previousStateStack;
	
	private IdentityHashSet<SelectStore> previousStateVariables;
	private Set<SelectStore> variablesInAlias;

	
	
	private Stack<String> previousStateOperationSequence;
	private Map<SelectStore, VarData> previousStateVarSequences;
	private Map<ArrayVariable, VarData> previousStateScramble;
	
	private Map<SelectStore, VarData> aliasVarSequences;
	private Map<ArrayVariable, VarData> aliasScrambled;
	
	public Alias(String symbol, Expression expression){
		this.symbol = symbol;
		this.expression = expression;
		
		this.explore = true;
		
		//Factorizer State
		this.previousStateStack = null;
		this.previousStateVariables = null;
		
		this.factorizerState = null;
		this.variablesInAlias = null;

		//Renamer State
		this.previousStateOperationSequence = null;
		this.previousStateVarSequences = null;
		this.previousStateScramble = null;
		
		this.aliasVarSequences = null;
		this.aliasScrambled = null;
		
	}

	@Override
	public void accept(Visitor visitor) throws VisitorException {
		visitor.preVisit(this);
		if(explore){
			expression.accept(visitor);
		}
		visitor.postVisit(this);
	}
	
	public void exploreSubexpression(boolean explore){
		this.explore = explore;
	}

	@Override
	public boolean equals(Object object) {
		if(object instanceof Alias){
			if(this.symbol.equals(((Alias) object).getSymbol())){
				return true;
			}
		}
		return false;
	}
	
	@Override
	public int hashCode(){
		return this.symbol.hashCode();
	}

	@Override
	public String toString() {
		if(expression instanceof Operation){
			return expression.toString();
		}
		return expression.toString();
	}
	
	public String getSymbol(){
		return this.symbol;
	}

	public boolean hasFactorizerInformation() {
		return (this.factorizerState!=null);
	}
	
	public boolean hasRenamerInformation(){
		return (aliasVarSequences!=null && aliasScrambled!=null);
	}

	public void setFactorizerAliasInformation(AVStack state, Set<SelectStore> variables) {
		this.factorizerState = state;
		this.variablesInAlias = variables;
	}
	
	public void setFactorizerVisitorState(AVStack state, IdentityHashSet<SelectStore> currentConjunctVars){
		this.previousStateStack = state;
		this.previousStateVariables = currentConjunctVars;
	}
	
	/*
	 * State of the visitor
	 */
	public AVStack getFactorizerStateStack(){
		return this.previousStateStack;
	}
	
	public AVStack getRenamerStateStack(){
		return this.previousStateStack;
	}
	
	public IdentityHashSet<SelectStore> getFactorizerStateVariables(){
		return this.previousStateVariables;
	}
	
	/*
	 * Information about the expression
	 */
	public AVStack getFactorizerAliasStack(){
		return this.factorizerState.clone();
	}

	public Set<SelectStore> getFactorizerAliasVariblesUsed(){
		return this.variablesInAlias;
	}

	public void setRenamerVisitorState(AVStack store, Stack<String> operationSequence, Map<SelectStore, VarData> varSequences, Map<ArrayVariable, VarData> scrambled) {
		this.previousStateStack = store;
		this.previousStateOperationSequence = operationSequence;
		this.previousStateVarSequences = varSequences;
		this.previousStateScramble = scrambled;
		
	}
	
	public void setRenamerAliasInformation(Map<SelectStore, VarData> varSequences, Map<ArrayVariable, VarData> scrambled){
		this.aliasVarSequences = varSequences;
		this.aliasScrambled = scrambled;
	}

	public Stack<String> getRenamedOperationSequence() {
		return this.previousStateOperationSequence;
	}

	public Map<SelectStore, VarData> getRenamedVarSequences() {
		return this.previousStateVarSequences;
	}

	public Map<ArrayVariable, VarData> getRenamedScrambled() {
		return this.previousStateScramble;
	}
	
	public Map<SelectStore, VarData> getRenamedAliasVarSequences(){
		return this.aliasVarSequences;
	}
	
	public Map<ArrayVariable, VarData> getRenamedAliasScrambled(){
		return this.aliasScrambled;
	}

	public Expression getExpression() {
		return this.expression;
	}
	
	
}
