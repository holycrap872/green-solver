package za.ac.sun.cs.green.resources;

import java.util.HashSet;
import java.util.Set;

/*
 * A wrapper for the HashSet data structure that implements
 * hashing based on the location of the hashset in memory,
 * making it faster than the regular hashset, which hashes
 * on the elements in the set. 
 */
public class IdentityHashSet<T> extends HashSet<T>{
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public IdentityHashSet(Set<T> collapsed) {
		super(collapsed);
	}
	
	public IdentityHashSet(){
		super();
	}

	public IdentityHashSet(int size) {
		super(size); 	//me
	}

	@Override
	public int hashCode(){
		return System.identityHashCode(this);
	}
	
	public boolean equals(Object o){
		return ((Object)this).equals(o);
	}

}
