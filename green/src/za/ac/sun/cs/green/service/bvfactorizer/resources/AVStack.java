package za.ac.sun.cs.green.service.bvfactorizer.resources;

import java.util.Deque;
import java.util.LinkedList;

import za.ac.sun.cs.green.expr.ArrayVariable;

/*
 * This class keeps track of the last array variable seen
 * in a subexpression.  This is needed because klee has operations
 * like store(store(store(...))) where the particular array the
 * first store is interacting with isn't known until we have explore
 * its subexpressions.
 * 
 *  Things get complicated because there are also select statements
 *  that can be mixed in.  For a full explanation of how this class
 *  us used, see BVFactorExpression.
 */
public class AVStack implements Cloneable{
	private Deque<ArrayVariable> stack;
	
	public AVStack(){
		stack = new LinkedList<ArrayVariable>();
		stack.addFirst(null);
	}
	
	public ArrayVariable pop(){
		return stack.removeFirst();
	}
	
	public ArrayVariable peek(){
		return stack.peekFirst();
	}
	
	public void push(ArrayVariable av){
		stack.addFirst(av);
	}
	
	public void stickOntoEnd(AVStack other){
		while(other.stack.peekLast()==null){
			other.stack.removeLast();
		}
		while(!other.stack.isEmpty()){
			stack.push(other.stack.removeLast());
		}
	}
	
	@Override
	public AVStack clone(){
		AVStack ret = new AVStack();
		ret.stack = new LinkedList<ArrayVariable>(this.stack);
		
		return ret;
	}
	
	public String toString(){
		return stack.toString();
	}
	
}