package za.ac.sun.cs.green.klee;

import static org.junit.Assert.*;

import java.util.HashSet;
import java.util.Properties;

import org.junit.Test;

import za.ac.sun.cs.green.Constants;
import za.ac.sun.cs.green.service.bvfactorizer.resources.UndeterminedArrayMerger;

public class UndeterminedArrayMergerTest {

	@Test
	public void test01() {
		Properties prop = new Properties();
		try{
			UndeterminedArrayMerger.mergeNecessary(null, null, null, null, null, null, prop);
		}catch(Exception e){
			assertTrue(true);
			return;
		}
		assertTrue(false);
	}
	
	@Test
	public void test02() {
		Properties prop = new Properties();
		prop.setProperty(Constants.SMASH_FACTORS_KEY, "smash_dont_merge_experimental");

		UndeterminedArrayMerger.mergeNecessary(null, null, null, new HashSet<za.ac.sun.cs.green.service.bvfactorizer.resources.SelectStore>(), null, null, prop);		
	}
}
