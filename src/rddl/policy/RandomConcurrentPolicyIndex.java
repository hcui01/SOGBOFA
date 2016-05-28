/**
 * RDDL: Implements a random policy for a domain with concurrent actions
 *       (allows mixed action types)
 * 
 * @author Tom Walsh (thomasjwalsh@gmail.com)
 * @author Scott Saner (ssanner@gmail.com)
 * @version 11/7/10
 *
 **/

package rddl.policy;

import java.lang.reflect.InvocationTargetException;
import java.util.*;
import java.util.Map.Entry;

import rddl.*;
import rddl.RDDL.*;
import util.Permutation;

public class RandomConcurrentPolicyIndex extends Policy {
		
	//public int NUM_CONCURRENT_ACTIONS = 8; // Max number of non-default concurrent actions
	public int MAX_INT_VALUE = 5; // Max int value to use when selecting random action
	public double MAX_REAL_VALUE = 5.0d; // Max real value to use when selecting random action
	public double countRandom = 0;
	public double countComb = 0;
	public double countEfficientCom = 0;
	public double countPassConst = 0;
	final double conflictCheck = 0.66;
	
	public HashMap<ArrayList<Integer>, Boolean> already;
	public long possibleComb;
	public int[] endingPoint;
	public double[] combNumEnding;
	public double[] countNumBits = new double[20];
	
	
	//prepare data for a state
	public RandomConcurrentPolicyIndex (State state) throws EvalException { 
		already = new HashMap<ArrayList<Integer>, Boolean>();
		//no matter what we need to get ready for generate random action
		int numSingleAction = 0;
		for (PVAR_NAME p : state._alActionNames) {
			ArrayList<ArrayList<LCONST>> term = state.generateAtoms(p);
			numSingleAction += term.size();
		}
		possibleComb = 0;
		for (int m = 1; m <= state._nMaxNondefActions; m++) {
			// cal how many m-combs exist
			double temp = 1;
			for (int i = 0; i < m; i++) {
				temp *= (numSingleAction - i);
			}
			for (int i = 2; i <= m; i++) {
				temp /= i;
			}
			possibleComb += temp;
		}
		possibleComb++;
		// preparation before generate random action
		int numOfAction = state._alActionNames.size();
		endingPoint = new int[numOfAction];
		PVAR_NAME actionName[] = new PVAR_NAME[numOfAction];
		int end = -1;
		ArrayList<ArrayList<ArrayList<LCONST>>> terms = new ArrayList<ArrayList<ArrayList<LCONST>>>();
		for (int i = 0; i < numOfAction; i++) {
			PVAR_NAME p = state._alActionNames.get(i);
			actionName[i] = p;
			ArrayList<ArrayList<LCONST>> term = state.generateAtoms(p);
			terms.add(state.generateAtoms(p));
			end += term.size();
			endingPoint[i] = end;
		}

		// with what porb we choose the number of actions participating into a
		// comb
		combNumEnding = new double[state._nMaxNondefActions + 1];
		combNumEnding[0] = 1;
		int numOfsingleAction = endingPoint[numOfAction - 1] + 1;
		for (int m = 1; m <= state._nMaxNondefActions; m++) {
			// cal how many m-combs exist
			double temp = 1;
			for (int i = 0; i < m; i++) {
				temp *= (numOfsingleAction - i);
			}
			for (int i = 2; i <= m; i++) {
				temp /= i;
			}
			combNumEnding[m] = combNumEnding[m - 1] + temp;
		}
		for (int m = 0; m <= state._nMaxNondefActions; m++) {
			combNumEnding[m] /= combNumEnding[state._nMaxNondefActions];
		}
	}
	
	//because possibleCOmb, endingPoint, combNumEnding are all variables that only for read
	//so we can directly point these members to the already generated object members
	//only already needs to be newed 
	public RandomConcurrentPolicyIndex (RandomConcurrentPolicyIndex rm) throws EvalException {
		possibleComb = rm.possibleComb;
		endingPoint = rm.endingPoint;
		combNumEnding = rm.combNumEnding;
		already = new HashMap<ArrayList<Integer>, Boolean>();
	}
	
	public RandomConcurrentPolicyIndex(String instance_name) {
		super(instance_name);
	}

	
	
	public void setActionMaxIntValue(int max_int_value) {
		MAX_INT_VALUE = max_int_value;
	}
	
	public void setActionMaxRealValue(double max_real_value) {
		MAX_REAL_VALUE = max_real_value; 
	}
	
	boolean CheckSameTerm(ArrayList<LCONST> termA, ArrayList<LCONST> termB){
		boolean ifSame = true;
		
		for(LCONST aterm: termA){
			boolean ifExist = false;
			for(LCONST bterm: termB){
				if(aterm.equals(bterm)){
					ifExist = true;
					break;
				}
			}
			if(!ifExist){
				ifSame = false;
				break;
			}
		}
		return ifSame;
	}
	
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {
		already = new HashMap<ArrayList<Integer>, Boolean>();
		//no matter what we need to get ready for generate random action
		int numSingleAction = 0;
		for (PVAR_NAME p : s._alActionNames) {
			ArrayList<ArrayList<LCONST>> term = s.generateAtoms(p);
			numSingleAction += term.size();
		}
		possibleComb = 0;
		for (int m = 1; m <= s._nMaxNondefActions; m++) {
			// cal how many m-combs exist
			double temp = 1;
			for (int i = 0; i < m; i++) {
				temp *= (numSingleAction - i);
			}
			for (int i = 2; i <= m; i++) {
				temp /= i;
			}
			possibleComb += temp;
		}
		possibleComb++;
		// preparation before generate random action
		int numOfAction = s._alActionNames.size();
		endingPoint = new int[numOfAction];
		PVAR_NAME actionName[] = new PVAR_NAME[numOfAction];
		int end = -1;
		ArrayList<ArrayList<ArrayList<LCONST>>> terms = new ArrayList<ArrayList<ArrayList<LCONST>>>();
		for (int i = 0; i < numOfAction; i++) {
			PVAR_NAME p = s._alActionNames.get(i);
			actionName[i] = p;
			ArrayList<ArrayList<LCONST>> term = s.generateAtoms(p);
			terms.add(s.generateAtoms(p));
			end += term.size();
			endingPoint[i] = end;
		}

		// with what porb we choose the number of actions participating into a
		// comb
		combNumEnding = new double[s._nMaxNondefActions + 1];
		combNumEnding[0] = 1;
		int numOfsingleAction = endingPoint[numOfAction - 1] + 1;
		for (int m = 1; m <= s._nMaxNondefActions; m++) {
			// cal how many m-combs exist
			double temp = 1;
			for (int i = 0; i < m; i++) {
				temp *= (numOfsingleAction - i);
			}
			for (int i = 2; i <= m; i++) {
				temp /= i;
			}
			combNumEnding[m] = combNumEnding[m - 1] + temp;
		}
		for (int m = 0; m <= s._nMaxNondefActions; m++) {
			combNumEnding[m] /= combNumEnding[s._nMaxNondefActions];
		}
		return getCAction(s);
	}
	

	//concrete state
	//get concrete action with no duplication
	//set if clear already data after getting action
	public ArrayList<PVAR_INST_DEF> getCAction(State s)throws EvalException {
		while (true) {
			// alrady generate all leal actions
			// in this case return a wried action, with the assignment false
			if (already.size() == possibleComb) {
				ArrayList<PVAR_INST_DEF> actions = new ArrayList<RDDL.PVAR_INST_DEF>();
				actions.add(new PVAR_INST_DEF("", false,
						new ArrayList<LCONST>()));
				return actions;
			}
			// retry
			ArrayList<Integer> finalDecision = new ArrayList<Integer>();

			// find how many actions should participate
			int numOfParticipat = 0;
			double dice = _random.nextDouble();
			for (int i = 0; i <= s._nMaxNondefActions; i++) {
				if ((i - 1 < 0 || combNumEnding[i - 1] < dice)
						&& combNumEnding[i] >= dice) {
					numOfParticipat = i;
					break;
				}
			}

			countNumBits[numOfParticipat]++;

			// find comb
			if (numOfParticipat == 0) {
				if (!already.containsKey(new ArrayList<Integer>())) {
					already.put(new ArrayList<Integer>(), true);
					return new ArrayList<RDDL.PVAR_INST_DEF>();
				} else {
					continue;
				}
			}
			int maxIndex = endingPoint[s._alActionNames.size() - 1];

			// generate numofParticapte independent single int
			for (int i = 0; i < numOfParticipat; i++) {
				boolean ifRepeat = true;
				while (ifRepeat) {
					int temp = _random.nextInt(maxIndex + 1);
					if (!finalDecision.contains(temp)) {
						if (finalDecision.size() == 0) {
							finalDecision.add(temp);
						} else {
							int insertPosition = finalDecision.size();
							for (int j = 0; j < finalDecision.size(); j++) {
								if ((temp < finalDecision.get(j) && (j == 0 || temp > finalDecision
										.get(j - 1)))) {
									insertPosition = j;
									break;
								}
							}
							finalDecision.add(insertPosition, temp);
						}
						ifRepeat = false;
					}
					countRandom++;
				}
			}

			countComb++;

			// find new comb then break
			if (!already.containsKey(finalDecision)) {
				countEfficientCom++;
				already.put(finalDecision, true);
				// get action from decision
				ArrayList<PVAR_INST_DEF> actions = new ArrayList<PVAR_INST_DEF>();
				for (Integer i : finalDecision) {
					for (int j = 0; j < endingPoint.length; j++) {
						if ((j - 1 < 0 || endingPoint[j - 1] < i)
								&& endingPoint[j] >= i) {
							int termIndex = j - 1 < 0 ? i : i
									- endingPoint[j - 1] - 1;
							PVAR_NAME p = s._alActionNames.get(j);
							actions.add(new PVAR_INST_DEF(p._sPVarName,
									(Object) true, s.generateAtoms(p).get(
											termIndex)));
							break;
						}
					}
				}
				boolean passed_constraints = true;
				try {
					s.checkStateActionConstraints(actions);
				} catch (EvalException e) {
					// Got an eval exception, constraint violated
					passed_constraints = false;
				}
				if (passed_constraints) {
					countPassConst++;
					return actions;
				}
			}
		}
	}
	
	//concrete state
	// get concrete number action with no duplication
	// set if clear already data after getting action
	public ArrayList<Integer> getNAction(State s) throws EvalException {
		while (true) {
			// alrady generate all leal actions
			// in this case return a wried action, with the assignment false
			if (already.size() == possibleComb) {
				ArrayList<Integer> actions = new ArrayList<Integer>();
				actions.add(-1);
				return actions;
			}
			// retry
			ArrayList<Integer> finalDecision = new ArrayList<Integer>();

			// find how many actions should participate
			int numOfParticipat = 0;
			double dice = _random.nextDouble();
			for (int i = 0; i <= s._nMaxNondefActions; i++) {
				if ((i - 1 < 0 || combNumEnding[i - 1] < dice)
						&& combNumEnding[i] >= dice) {
					numOfParticipat = i;
					break;
				}
			}

			countNumBits[numOfParticipat]++;

			// find comb
			if (numOfParticipat == 0) {
				if (!already.containsKey(new ArrayList<Integer>())) {
					already.put(new ArrayList<Integer>(), true);
					return new ArrayList<Integer>();
				} else {
					continue;
				}
			}
			int maxIndex = endingPoint[s._alActionNames.size() - 1];

			// generate numofParticapte independent single int
			for (int i = 0; i < numOfParticipat; i++) {
				boolean ifRepeat = true;
				while (ifRepeat) {
					int temp = _random.nextInt(maxIndex + 1);
					if (!finalDecision.contains(temp)) {
						if (finalDecision.size() == 0) {
							finalDecision.add(temp);
						} else {
							int insertPosition = finalDecision.size();
							for (int j = 0; j < finalDecision.size(); j++) {
								if ((temp < finalDecision.get(j) && (j == 0 || temp > finalDecision
										.get(j - 1)))) {
									insertPosition = j;
									break;
								}
							}
							finalDecision.add(insertPosition, temp);
						}
						ifRepeat = false;
					}
					countRandom++;
				}
			}

			countComb++;

			// find new comb then break
			if (!already.containsKey(finalDecision)) {
				countEfficientCom++;
				already.put(finalDecision, true);
				// get action from decision
				ArrayList<PVAR_INST_DEF> actions = new ArrayList<PVAR_INST_DEF>();
				for (Integer i : finalDecision) {
					for (int j = 0; j < endingPoint.length; j++) {
						if ((j - 1 < 0 || endingPoint[j - 1] < i)
								&& endingPoint[j] >= i) {
							int termIndex = j - 1 < 0 ? i : i
									- endingPoint[j - 1] - 1;
							PVAR_NAME p = s._alActionNames.get(j);
							actions.add(new PVAR_INST_DEF(p._sPVarName,
									(Object) true, s.generateAtoms(p).get(
											termIndex)));
							break;
						}
					}
				}
				boolean passed_constraints = true;
				try {
					s.checkStateActionConstraints(actions);
				} catch (EvalException e) {
					// Got an eval exception, constraint violated
					passed_constraints = false;
				}
				if (passed_constraints) {
					countPassConst++;
					return finalDecision;
				}
			}
		}
	}
	
	//concrete state
	// get the # of concrete action with duplication
	public ArrayList<Integer> getNActionDup(State s) throws EvalException {
		
			// retry
			ArrayList<Integer> finalDecision = new ArrayList<Integer>();

			// find how many actions should participate
			int numOfParticipat = 0;
			double dice = _random.nextDouble();
			for (int i = 0; i <= s._nMaxNondefActions; i++) {
				if ((i - 1 < 0 || combNumEnding[i - 1] < dice)
						&& combNumEnding[i] >= dice) {
					numOfParticipat = i;
					break;
				}
			}

			countNumBits[numOfParticipat]++;

			// find comb
			if (numOfParticipat == 0) {
				
				return new ArrayList<Integer>();
				
			}
			int maxIndex = endingPoint[s._alActionNames.size() - 1];

			// generate numofParticapte independent single int
			for (int i = 0; i < numOfParticipat; i++) {
				boolean ifRepeat = true;
				while (ifRepeat) {
					int temp = _random.nextInt(maxIndex + 1);
					if (!finalDecision.contains(temp)) {
						if (finalDecision.size() == 0) {
							finalDecision.add(temp);
						} else {
							int insertPosition = finalDecision.size();
							for (int j = 0; j < finalDecision.size(); j++) {
								if ((temp < finalDecision.get(j) && (j == 0 || temp > finalDecision
										.get(j - 1)))) {
									insertPosition = j;
									break;
								}
							}
							finalDecision.add(insertPosition, temp);
						}
						ifRepeat = false;
					}
					countRandom++;
				}
			}

			countComb++;

			
		return finalDecision;
	}
	
	//concrete state
	// get concrete action with duplication
	//this is used for roll out
	public ArrayList<PVAR_INST_DEF> getCActionDup(State s) throws EvalException {
		HashMap<ArrayList<Integer>, Boolean> tempAlrady = new HashMap<ArrayList<Integer>, Boolean>();
		while (true) {
			// alrady generate all leal actions
			// in this case return a wried action, with the assignment false
			if (tempAlrady.size() == possibleComb) {
				ArrayList<PVAR_INST_DEF> actions = new ArrayList<RDDL.PVAR_INST_DEF>();
				actions.add(new PVAR_INST_DEF("", false, new ArrayList<LCONST>()));
				return actions;
			}
			// retry
			ArrayList<Integer> finalDecision = new ArrayList<Integer>();

			// find how many actions should participate
			int numOfParticipat = 0;
			double dice = _random.nextDouble();
			for (int i = 0; i <= s._nMaxNondefActions; i++) {
				if ((i - 1 < 0 || combNumEnding[i - 1] < dice)
						&& combNumEnding[i] >= dice) {
					numOfParticipat = i;
					break;
				}
			}

			countNumBits[numOfParticipat]++;

			// find comb
			if (numOfParticipat == 0) {
				if (!tempAlrady.containsKey(new ArrayList<Integer>())) {
					tempAlrady.put(new ArrayList<Integer>(), true);
					return new ArrayList<RDDL.PVAR_INST_DEF>();
				} else {
					continue;
				}
			}
			int maxIndex = endingPoint[s._alActionNames.size() - 1];

			// generate numofParticapte independent single int
			for (int i = 0; i < numOfParticipat; i++) {
				boolean ifRepeat = true;
				while (ifRepeat) {
					int temp = _random.nextInt(maxIndex + 1);
					if (!finalDecision.contains(temp)) {
						if (finalDecision.size() == 0) {
							finalDecision.add(temp);
						} else {
							int insertPosition = finalDecision.size();
							for (int j = 0; j < finalDecision.size(); j++) {
								if ((temp < finalDecision.get(j) && (j == 0 || temp > finalDecision
										.get(j - 1)))) {
									insertPosition = j;
									break;
								}
							}
							finalDecision.add(insertPosition, temp);
						}
						ifRepeat = false;
					}
					countRandom++;
				}
			}

			countComb++;

			// find new comb then break
			if (!tempAlrady.containsKey(finalDecision)) {
				countEfficientCom++;
				tempAlrady.put(finalDecision, true);
				// get action from decision
				ArrayList<PVAR_INST_DEF> actions = new ArrayList<PVAR_INST_DEF>();
				for (Integer i : finalDecision) {
					for (int j = 0; j < endingPoint.length; j++) {
						if ((j - 1 < 0 || endingPoint[j - 1] < i)
								&& endingPoint[j] >= i) {
							int termIndex = j - 1 < 0 ? i : i
									- endingPoint[j - 1] - 1;
							PVAR_NAME p = s._alActionNames.get(j);
							actions.add(new PVAR_INST_DEF(p._sPVarName,
									(Object) true, s.generateAtoms(p).get(
											termIndex)));
							break;
						}
					}
				}
				boolean passed_constraints = true;
				try {
					s.checkStateActionConstraints(actions);
				} catch (EvalException e) {
					// Got an eval exception, constraint violated
					passed_constraints = false;
				}
				if (passed_constraints) {
					countPassConst++;
					return actions;
				}
			}
		}
	}
	
	
	
	//agg state
	//get concrete action with no duplication
	public ArrayList<PVAR_INST_DEF> getCAction(AState s) throws EvalException {
		
		while(true){
			//retry
			ArrayList<Integer> finalDecision = new ArrayList<Integer>();
			
			//find how many actions should participate
			int numOfParticipat = 0;
			double dice = _random.nextDouble();
			for(int i = 0; i <= s._nMaxNondefActions; i ++){
				if((i - 1 < 0 || combNumEnding[i-1] < dice) && combNumEnding[i] >= dice){
					numOfParticipat = i;
					break;
				}
			}
			
			countNumBits[numOfParticipat] ++;
			
			//find comb
			if(numOfParticipat == 0 ){
				if(!already.containsKey(new ArrayList<Integer>())){
					already.put(new ArrayList<Integer>(), true);
					return new ArrayList<RDDL.PVAR_INST_DEF>();
				}
				else{
					continue;
				}
			}
			int maxIndex = endingPoint[s._alActionNames.size()-1];
			
			// generate numofParticapte independent single int
			for (int i = 0; i < numOfParticipat; i++) {
				boolean ifRepeat = true;
				while (ifRepeat) {
					int temp = _random.nextInt(maxIndex+1);
					if (!finalDecision.contains(temp)) {
						if(finalDecision.size() == 0){
							finalDecision.add(temp);
						}
						else{
							int insertPosition = finalDecision.size();
							for (int j = 0; j < finalDecision.size(); j++) {
								if ((temp < finalDecision.get(j) && (j == 0 || temp > finalDecision
										.get(j - 1)))) {
									insertPosition = j;
									break;
								}
							}
							finalDecision.add(insertPosition, temp);
						}
						ifRepeat = false;
					}
					countRandom ++;
				}
			}
			
			countComb ++;
			
			//find new comb then break
			if(!already.containsKey(finalDecision)){
				countEfficientCom ++;
				
				already.put(finalDecision, true);
				//get action from decision
				ArrayList<PVAR_INST_DEF> actions = new ArrayList<PVAR_INST_DEF>();
				for(Integer i : finalDecision){
					for(int j = 0; j < endingPoint.length; j ++){
						if((j-1 < 0 || endingPoint[j-1] < i) && endingPoint[j] >= i){
							int termIndex = j-1<0 ? i : i - endingPoint[j-1] - 1;
							PVAR_NAME p = s._alActionNames.get(j);
							if(actions.size() == 5 || termIndex == 6 ){
								int a = 1;
							}
							actions.add(new PVAR_INST_DEF(p._sPVarName, (Object)true, s.generateAtoms(p).get(termIndex)));
							break;
						}
					}
				}
				double passed_constraints = -1;
				passed_constraints = s.checkStateActionConstraints(actions);
				if(passed_constraints > 0.5){
					countPassConst ++;
					return actions;
				}
				//System.out.println(actions + " " + passed_constraints);
			}
		}
	}
	
	//agg state
	//get concrete action with duplication
	public ArrayList<PVAR_INST_DEF> getCActionDup(AState s) throws EvalException {
		HashMap<ArrayList<Integer>, Boolean> tempAlrady = new HashMap<ArrayList<Integer>, Boolean>();
		while (true) {
			// retry
			ArrayList<Integer> finalDecision = new ArrayList<Integer>();

			// find how many actions should participate
			int numOfParticipat = 0;
			double dice = _random.nextDouble();
			for (int i = 0; i <= s._nMaxNondefActions; i++) {
				if ((i - 1 < 0 || combNumEnding[i - 1] < dice)
						&& combNumEnding[i] >= dice) {
					numOfParticipat = i;
					break;
				}
			}

			countNumBits[numOfParticipat]++;

			// find comb
			if (numOfParticipat == 0) {
				if (!tempAlrady.containsKey(new ArrayList<Integer>())) {
					tempAlrady.put(new ArrayList<Integer>(), true);
					return new ArrayList<RDDL.PVAR_INST_DEF>();
				} else {
					continue;
				}
			}
			int maxIndex = endingPoint[s._alActionNames.size() - 1];

			// generate numofParticapte independent single int
			for (int i = 0; i < numOfParticipat; i++) {
				boolean ifRepeat = true;
				while (ifRepeat) {
					int temp = _random.nextInt(maxIndex + 1);
					if (!finalDecision.contains(temp)) {
						if (finalDecision.size() == 0) {
							finalDecision.add(temp);
						} else {
							int insertPosition = finalDecision.size();
							for (int j = 0; j < finalDecision.size(); j++) {
								if ((temp < finalDecision.get(j) && (j == 0 || temp > finalDecision
										.get(j - 1)))) {
									insertPosition = j;
									break;
								}
							}
							finalDecision.add(insertPosition, temp);
						}
						ifRepeat = false;
					}
					countRandom++;
				}
			}

			countComb++;

			// find new comb then break
			if (!tempAlrady.containsKey(finalDecision)) {
				countEfficientCom++;

				tempAlrady.put(finalDecision, true);
				// get action from decision
				ArrayList<PVAR_INST_DEF> actions = new ArrayList<PVAR_INST_DEF>();
				for (Integer i : finalDecision) {
					for (int j = 0; j < endingPoint.length; j++) {
						if ((j - 1 < 0 || endingPoint[j - 1] < i)
								&& endingPoint[j] >= i) {
							int termIndex = j - 1 < 0 ? i : i
									- endingPoint[j - 1] - 1;
							PVAR_NAME p = s._alActionNames.get(j);
							if (actions.size() == 5 || termIndex == 6) {
								int a = 1;
							}
							actions.add(new PVAR_INST_DEF(p._sPVarName,
									(Object) true, s.generateAtoms(p).get(
											termIndex)));
							break;
						}
					}
				}
				double passed_constraints = -1;
				passed_constraints = s.checkStateActionConstraints(actions);
				if (passed_constraints > 0.5) {
					countPassConst++;
					return actions;
				}
				// System.out.println(actions + " " + passed_constraints);
			}
		}
	}
	
	//agg state
	//used for roll out, e.g. we don't care generate same action at same state
	// get aggregate action by sampling without replacement
	// here we only use random generating
	// we stop when conflictchek * numPossibleComb actions are generated or meet
	// the requirements
	public ArrayList<PVAR_INST_DEF> getAActionDup(AState s, int numOfSample)
			throws EvalException {
		RandomConcurrentPolicyIndex conGen = new RandomConcurrentPolicyIndex(this);
		ArrayList<PVAR_INST_DEF> actions = new ArrayList<PVAR_INST_DEF>();
		final double conflictCheck = 0.66;
		int realNumSample = 0;

		// get n concrete actions and cal the porpotion of each bit
		HashMap<PVAR_INST_DEF, Double> bitProb = new HashMap<PVAR_INST_DEF, Double>();
		for (int i = 1; i <= numOfSample; i++) {
			ArrayList<PVAR_INST_DEF> concreteAct = conGen.getCAction(s);
			realNumSample++;
			// System.out.println("already size: " + tmpAlready.size() +
			// " passed: " + realNumSample);
			for (PVAR_INST_DEF bit : concreteAct) {
				if (!bitProb.containsKey(bit)) {
					bitProb.put(bit, 1.0);
				} else {
					double tmp2 = bitProb.get(bit);
					bitProb.put(bit, tmp2 + 1);
				}
			}
			if (conGen.already.size() > possibleComb * conflictCheck) {
				break;
			}
		}
		Iterator<Entry<PVAR_INST_DEF, Double>> iter = bitProb.entrySet()
				.iterator();
		while (iter.hasNext()) {
			Map.Entry entry = (Map.Entry) iter.next();
			double theProb = (Double) entry.getValue() / realNumSample;
			PVAR_INST_DEF theBit = (PVAR_INST_DEF) entry.getKey();
			actions.add(new PVAR_INST_DEF(theBit._sPredName._sPVarName,
					(Object) theProb, theBit._alTerms));
		}
		return actions;
	}
	
	public ArrayList<PVAR_INST_DEF> getAActionDupWithManySam(AState s, int numOfSample)
			throws EvalException {
		RandomConcurrentPolicyIndex conGen = new RandomConcurrentPolicyIndex(this);
		ArrayList<PVAR_INST_DEF> actions = new ArrayList<PVAR_INST_DEF>();
		final double conflictCheck = 0.66;
		int realNumSample = 0;

		// get n concrete actions and cal the porpotion of each bit
		HashMap<PVAR_INST_DEF, Double> bitProb = new HashMap<PVAR_INST_DEF, Double>();
		for (int i = 1; i <= numOfSample; i++) {
			ArrayList<PVAR_INST_DEF> concreteAct = conGen.getCActionDup(s);
			realNumSample++;
			// System.out.println("already size: " + tmpAlready.size() +
			// " passed: " + realNumSample);
			for (PVAR_INST_DEF bit : concreteAct) {
				if (!bitProb.containsKey(bit)) {
					bitProb.put(bit, 1.0);
				} else {
					double tmp2 = bitProb.get(bit);
					bitProb.put(bit, tmp2 + 1);
				}
			}
		}
		Iterator<Entry<PVAR_INST_DEF, Double>> iter = bitProb.entrySet()
				.iterator();
		while (iter.hasNext()) {
			Map.Entry entry = (Map.Entry) iter.next();
			double theProb = (Double) entry.getValue() / realNumSample;
			PVAR_INST_DEF theBit = (PVAR_INST_DEF) entry.getKey();
			actions.add(new PVAR_INST_DEF(theBit._sPredName._sPVarName,
					(Object) theProb, theBit._alTerms));
		}
		return actions;
	}
	
	public ArrayList<PVAR_INST_DEF> getAActionDupTest(AState s, int numOfSample)
			throws EvalException {
		RandomConcurrentPolicyIndex conGen = new RandomConcurrentPolicyIndex(this);
		ArrayList<PVAR_INST_DEF> actions = new ArrayList<PVAR_INST_DEF>();
		final double conflictCheck = 0.66;
		int realNumSample = 0;

		// get n concrete actions and cal the porpotion of each bit
		HashMap<PVAR_INST_DEF, Double> bitProb = new HashMap<PVAR_INST_DEF, Double>();
		for (int i = 1; i <= numOfSample; i++) {
			ArrayList<PVAR_INST_DEF> concreteAct = conGen.getCAction(s);
			realNumSample++;
			// System.out.println("already size: " + tmpAlready.size() +
			// " passed: " + realNumSample);
			for (PVAR_INST_DEF bit : concreteAct) {
				if (!bitProb.containsKey(bit)) {
					bitProb.put(bit, 1.0);
				} else {
					double tmp2 = bitProb.get(bit);
					bitProb.put(bit, tmp2 + 1);
				}
			}

		}
		Iterator<Entry<PVAR_INST_DEF, Double>> iter = bitProb.entrySet()
				.iterator();
		while (iter.hasNext()) {
			Map.Entry entry = (Map.Entry) iter.next();
			double theProb = (Double) entry.getValue() / realNumSample;
			PVAR_INST_DEF theBit = (PVAR_INST_DEF) entry.getKey();
			actions.add(new PVAR_INST_DEF(theBit._sPredName._sPVarName,
					(Object) theProb, theBit._alTerms));
		}
		return actions;
	}
}
