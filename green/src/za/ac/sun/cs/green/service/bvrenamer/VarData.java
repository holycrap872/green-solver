package za.ac.sun.cs.green.service.bvrenamer;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import za.ac.sun.cs.green.expr.ArrayVariable;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.BitVectorConstant;


/*
 * Holds the information of the sequences of operations
 * that lead up to a variable in a priority queue.  When
 * asked, it returns this data in hashed form.
 */
public class VarData implements Comparable<Object>{
	
	private final ArrayVariable arrayName;
	private final Expression index;
	
	private ArrayVariable newArrayName;
	private Expression newIndex;
	
	private List<String> operations;
	private boolean hashGenerated;
	private int hash;
	
	public VarData(ArrayVariable arrayName, Expression index){
		this.arrayName = arrayName;
		this.index = index;
		this.operations = new ArrayList<String>(1000);
		this.hashGenerated = false;
	}
	
	public VarData(VarData other){
		this.arrayName = other.arrayName;
		this.index = other.index;
		this.operations = new ArrayList<String>(other.getOperations());
		this.hashGenerated = false;
	}
	
	public void setNewNameIndex(String name, int index){
		this.newArrayName = new ArrayVariable(name);
		this.newArrayName.setArrayDeclarations(arrayName.getIndexSize(), arrayName.getMemSizeBits());
		this.newIndex = new BitVectorConstant(new BigInteger(Integer.toString(index)), arrayName.getIndexSize().getValue());
	}
	
	protected List<String> getOperations(){
		return operations;
	}
	
	public ArrayVariable getOldName(){
		return this.arrayName;
	}
	
	public ArrayVariable getNewName(){
		return this.newArrayName;
	}
	
	public Expression getNewIndex(){
		return this.newIndex;
	}
	
	public String toString(){
		if(newIndex == null){
			return "OLD ARRAY Occurrences: "+this.operations.size()+", Name: "+arrayName.toString()+", Index: "+index.toString()+ ", Hash: "+this.hash;
		}
		return "NEW ARRAY: Occurrences: "+this.operations.size()+", Name: "+newArrayName.toString()+", Index: "+newIndex.toString() +", Hash: "+this.hash+", ID: "+this.getId();
	}
	
	public void addOperationSequence(String sequence){
		hashGenerated = false;
		operations.add(sequence);
	}
	
	private String getId(){
		StringBuilder id = new StringBuilder(100000);
		
		Collections.sort(operations);
		
		for(String s: operations){
			id.append(s);
		}
		return id.toString();
	}
	
	@Override
	public int hashCode(){
		if(!hashGenerated){
			hash = getId().hashCode();
			hashGenerated = true;
		}
		return hash;
	}
	
	@Override
	public int compareTo(Object o){
		VarData v = (VarData)o;
		int ret = new Integer(this.hashCode()).compareTo(v.hashCode());
		//ONLY IF they operations leading up to the individual variables are equal do we go based on index.
		//This is to handle situations like concat x y, where there would be no other way to give a canonical
		//ordering to the variables.
		if(ret==0){
			ret = this.index.toString().compareTo(v.index.toString());
		}
		return ret;
	}
	
	@Override
	public boolean equals(Object o){
		VarData v = (VarData)o;
		return new Integer(this.hashCode()).equals(v.hashCode());
	}

	public void mergeVarData(VarData oldV) {
		for(String sequence: oldV.operations){
			operations.add(sequence);
		}
		hashGenerated = false;		
	}

	public void prepend(String peek) {
		int i = 0;
		while(i<operations.size()){
			operations.set(i, operations.get(i)+peek);
			i ++;
		}
	}
}