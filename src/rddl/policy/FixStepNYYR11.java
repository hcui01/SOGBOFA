package rddl.policy;

import java.security.AllPermission;
import java.util.*;

import javax.naming.InitialContext;

import rddl.AState;
import rddl.EvalException;
import rddl.RDDL;
import rddl.RDDL.*;
import rddl.State;
import rddl.parser.parser;
import rddl.viz.GenericScreenDisplay;
import rddl.viz.NullScreenDisplay;
import rddl.viz.StateViz;
import rddl.RDDL.INSTANCE;
import rddl.RDDL.ENUM_TYPE_DEF;
import rddl.RDDL.LCONST;
import rddl.RDDL.LVAR;
import rddl.RDDL.PVARIABLE_DEF;
import rddl.RDDL.PVAR_INST_DEF;
import rddl.RDDL.PVAR_NAME;
import util.Permutation;

public class FixStepNYYR11 extends Policy {

	public int NUM_CONCURRENT_ACTIONS = 2; // Max number of non-default concurrent actions
	public int MAX_INT_VALUE = 5; // Max int value to use when selecting random action
	public double MAX_REAL_VALUE = 5.0d; // Max real value to use when selecting random action
	public int POSSIBLE_ACTIONS = 1000;  //max number of possible actions
	public int mode = 1; //1 for time 2 for number
	public int NUM_OF_ROLLOUT = 1000;
	double ipsino = 0.5f;
	double searchRatio = 1;
	double ratioOfJudgment = 20;
	long genAllThreshold = 40000;
	int numOfSample = 10;
	boolean ifPrint = false;
	double possibleComb = 0;
	final double MIN_DOUBLE_VALUE = -10000000000.0;
	
	public class Performance{			//record performance of each action
		public Performance(){
			accum_performance = 0;
			tryNumber = 0;
		}
		public Performance(double acc, int num, ArrayList<PVAR_INST_DEF> act){
			accum_performance = acc;
			tryNumber = num;
			evaluatingAction = act;
		}
		public ArrayList<PVAR_INST_DEF> evaluatingAction;
		public double accum_performance;
		public int tryNumber;
	};
	public class ConcurrencyPerformance{
		public double concurrencyAccumPerformance;
		public int concurrencyTryNumber;
		public ConcurrencyPerformance(){
			concurrencyAccumPerformance = 0;
			concurrencyTryNumber = 0;
		}
	}
	
	
	public FixStepNYYR11 () { 
		super();
	}
	
	public FixStepNYYR11(String instance_name) {
		super(instance_name);
	}

//	public void setNumConcurrentActions(int num_concurrent) {
//		NUM_CONCURRENT_ACTIONS = num_concurrent;
//	}
	
//	public void setActionMaxIntValue(int max_int_value) {
//		MAX_INT_VALUE = max_int_value;
//	}
	
//	public void setActionMaxRealValue(double max_real_value) {
//		MAX_REAL_VALUE = max_real_value; 
//	}
	
	class TwoInt{
		int actionIndex;
		int termIndex;
	}
	
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {
	/*
		HashMap<ArrayList<Integer>, Boolean> a= new HashMap<ArrayList<Integer>, Boolean>();
		ArrayList<Integer> in = new ArrayList<Integer>();
		in.add(1);
		in.add(2);
		in.add(3);
		ArrayList<Integer> in2 = new ArrayList<Integer>();
		in2.add(1);
		in2.add(2);
		in2.add(3);
		ArrayList<Integer> in3 = new ArrayList<Integer>();
		in3.add(1);
		in3.add(3);
		in3.add(2);
		a.put(in, true);
		a.put(in2, false);
		int c =0;
		if(a.containsKey(in)){
			c = 1;
		}
		if(a.containsKey(in2)){
			c = 1;
		}
		if(a.containsKey(in3)){
			c = 1;
		}
		c ++;
		*/
		//get the damin and parameters
		INSTANCE instance = rddl._tmInstanceNodes.get(_sInstanceName);
		DOMAIN domain = rddl._tmDomainNodes.get(instance._sDomain);
		NUM_CONCURRENT_ACTIONS = instance._nNonDefActions;
		
		/********************needs modification ************************/
		ArrayList<Performance> performanceRecords = new ArrayList<Performance>();
		//int recordsCounter = 0;
		/********************needs modification ************************/
		
		//count the times of simulation
		long t0 = System.currentTimeMillis();
		
		//how many simulations have been executed
		long simCounter = 0;
		
		//record which one is the current best
		int bestI = -1;
		
		//AALLPolicy _actionGenerator = new AALLPolicy();
		//_actionGenerator.setNumConcurrentActions(instance._nNonDefActions);
		RandomConcurrentPolicyIndex _actionGenerator = new RandomConcurrentPolicyIndex();
		
		//check if generate all actions
		//this is a complex computation which can be set with different parameters
		
		boolean ifGenerateAll = IfGenerateALL(s, instance, domain);
		ArrayList<ArrayList<PVAR_INST_DEF>> possibleFirstLevelAct = null;
		int numOfTopAct = 0;
		//if have checked all possible action at top level
		//just quit
		//if not generate all this var will not be used
		boolean ifCheckAll = false;
		boolean ifDirectlySearch = false;
		int numOfAction = 0;
		int endingPoint[] = null;
		double combNumEnding[] = null;
		RandomConcurrentPolicyIndex randomConcreteGen = null;
		HashMap<ArrayList<Integer>, Boolean> already = null;	
		
		//no matter what we need to get ready for generate random action
		//preparation before generate random action
		numOfAction = s._alActionNames.size();
		endingPoint = new int[numOfAction];
		PVAR_NAME actionName[] = new PVAR_NAME[numOfAction];
		int end = -1;
		ArrayList<ArrayList<ArrayList<LCONST>>> terms = new ArrayList<ArrayList<ArrayList<LCONST>>>();
		for(int i = 0; i < numOfAction; i ++){
			PVAR_NAME p = s._alActionNames.get(i);
			actionName[i] = p;
			ArrayList<ArrayList<LCONST>> term = s.generateAtoms(p);
			terms.add(s.generateAtoms(p));
			end += term.size();
			endingPoint[i] = end;
		}
		
		//with what porb we choose the number of actions participating into a comb
		combNumEnding = new double[s._nMaxNondefActions+1];
		combNumEnding[0] = 1;
		int numOfsingleAction = endingPoint[numOfAction-1] + 1;
		for(int m = 1; m <= s._nMaxNondefActions; m ++){
			//cal how many m-combs exist
			double temp = 1;
			for(int i = 0; i < m; i ++){
				temp *= (numOfsingleAction - i);
			}
			for(int i = 2; i <= m; i ++){
				temp /= i;
			}
			combNumEnding[m] = combNumEnding[m-1] + temp;
		}
		for(int m = 0; m <= s._nMaxNondefActions; m ++){
			combNumEnding[m] /= combNumEnding[s._nMaxNondefActions];
		}
		
		//new random action generator
		randomConcreteGen = new RandomConcurrentPolicyIndex();
		
		//new hashmap
		already = new HashMap<ArrayList<Integer>, Boolean>();
		
		if(ifGenerateAll){
			//generate all actions
			//this might be dangero
			System.out.println("Generate all actions! This might be dangerous!");
			possibleFirstLevelAct = findAllPossibleActions(s);
			numOfTopAct = possibleFirstLevelAct.size();
			System.out.println(numOfTopAct + " actions generated");
		}
		
		long timeForAct = 0;
		long t00 = System.currentTimeMillis();
		long simulationTime = 0;
		long sampleTime = 0;
		while(true){
			simCounter ++;
			//simulate for 3 seconds
			if(mode == 1){
				long t = System.currentTimeMillis();
				if(t - t0 > _timeAllowed){
					break;
				}
			}
			else if(mode == 2){
				if(simCounter > _timeAllowed){
					break;
				}
			}
			//initialize
			double accum_reward = 0.0d;
			double cur_discount = 1.0d;
			int h = 0;
			
			
			//tempState
			AState as = new AState();
			as.init(s);
			
			
			//store the first level actions
			ArrayList<PVAR_INST_DEF> _firstLevelAcs = new ArrayList<PVAR_INST_DEF>();
			
			//used to record the action at each step
			ArrayList<PVAR_INST_DEF> _randomAction = new ArrayList<PVAR_INST_DEF>();
			
			double dice = -1;
			int index = -1;
			//simulate once
			for( ; h < instance._nHorizon * searchRatio && currentRound + h <= instance._nHorizon; h++ ) {
				
				if(h == 0){
					if(ifCheckAll){
						ifDirectlySearch = true;
						dice = _random.nextDouble();
						if(dice > ipsino){
							index = bestI;
						}
						else{
							index = _random.nextInt(performanceRecords.size());
						}
						_randomAction = performanceRecords.get(index).evaluatingAction;
					}
					else{
						if(ifGenerateAll){
							// after checking each action once
							// we do totally random
							int rIndex = _random.nextInt(numOfTopAct);
							_randomAction = possibleFirstLevelAct.get(rIndex);
							possibleFirstLevelAct.set(rIndex, possibleFirstLevelAct.get(--numOfTopAct));
							if (simCounter == possibleFirstLevelAct.size()) {
								ifCheckAll = true;
							}
						}
						else{
							long act0 = System.currentTimeMillis();;
							_randomAction = randomConcreteGen.getActions(s, already, endingPoint, combNumEnding);
							timeForAct += System.currentTimeMillis() - act0;
							if(already.size() >= possibleComb){
								ifCheckAll = true;
							}
							if(ifPrint){
								System.out.println("Count random() per comb" + randomConcreteGen.countRandom / randomConcreteGen.countComb);
								System.out.println("1 out of " + randomConcreteGen.countComb / randomConcreteGen.countEfficientCom + " comb is useful");
								System.out.println("1 out of " + randomConcreteGen.countEfficientCom / randomConcreteGen.countPassConst + " comb is legal");
								for(int i = 0; i <= s._nMaxNondefActions; i ++){
									System.out.println(i + " action count: " + randomConcreteGen.countNumBits[i]);
								}
							}
						}
					}
					
				}
				else{
				
					//ANoopPolicy noop = new ANoopPolicy();
					//_randomAction = noop.getActions(as);
					long t000 = System.currentTimeMillis();
					HashMap<ArrayList<Integer>, Boolean> tempAlready = new HashMap<ArrayList<Integer>, Boolean>();
					_randomAction = _actionGenerator.getActions(as, tempAlready, numOfSample, possibleComb, endingPoint, combNumEnding);
					//System.out.println("Count random() per comb" + _actionGenerator.countRandom / _actionGenerator.countComb);
					//System.out.println("1 out of " + _actionGenerator.countComb / _actionGenerator.countEfficientCom + " comb is useful");
					//System.out.println("1 out of " + _actionGenerator.countEfficientCom / _actionGenerator.countPassConst + " comb is legal");
					sampleTime += System.currentTimeMillis() - t000;
					//System.out.println(_randomAction);
				}
				
				//record first level action if h == 0
				if( h == 0){
					_firstLevelAcs = _randomAction;
				}
				
				//compute next state
				//if(ifPrint){
				//	System.out.println(as._state);
				//}
				as.computeNextState(_randomAction, _random);
				
				//System.out.println(as._nextState);
				
				//compute reward
				/*
				if(h == 2){
					System.out.println(_firstLevelAcs);
					System.out.println(as._state);
				}
				*/
				double reward = ((Number)domain._exprReward.sample(new HashMap<LVAR,LCONST>(), 
					as, _random)).doubleValue();
				accum_reward += reward * cur_discount;
				cur_discount *= instance._dDiscount;
				as.advanceNextState();
			}
			//System.out.println(simCounter + " " + _firstLevelAcs + " " + accum_reward);
			
			//add performance to records
			//record performance
			if(bestI == -1 ){
				bestI = 0;
			}
			
			if(!ifDirectlySearch){
				if(index != -1){
					throw new EvalException("inde should be -1 when !ifdirectlysearch!");
				}
				performanceRecords.add(new Performance(accum_reward, 1, _firstLevelAcs));
				if(accum_reward > performanceRecords.get(bestI).accum_performance){
					bestI = performanceRecords.size() - 1;
				}
			}
			else{
				double ori = performanceRecords.get(index).accum_performance / performanceRecords.get(index).tryNumber;
				performanceRecords.get(index).tryNumber ++;
				performanceRecords.get(index).accum_performance += accum_reward;
				double late = performanceRecords.get(index).accum_performance / performanceRecords.get(index).tryNumber;
				if(index != bestI){
					if(late > performanceRecords.get(bestI).accum_performance / performanceRecords.get(bestI).tryNumber){
						bestI = index;
					}
				}
				if(index == bestI && late < ori){
					double maxScore = MIN_DOUBLE_VALUE;
					for(int i = 0; i < performanceRecords.size(); i ++){
						Performance p = performanceRecords.get(i);
						if(p.accum_performance / p.tryNumber > maxScore){
							maxScore = p.accum_performance / p.tryNumber;
							bestI = i;
						}
					}
				}
			}
			
			if(ifPrint){
				System.out.println(_firstLevelAcs + " " + accum_reward + " " + bestI);
			}
		}
		
		simulationTime += System.currentTimeMillis() - t00;
		//System.out.println(simulationTime + " " + sampleTime);
		
		
		//for(int i = 1; i <= recordsCounter; i ++){
		//	System.out.println(performanceRecords[i].evaluatingAction + " " + performanceRecords[i].accum_performance + " " + performanceRecords[i].tryNumber);
		//}
		
//		actions = new RandomConcurrentPolicy().getActions(s);
		if(bestI == -1){
			return new ArrayList<RDDL.PVAR_INST_DEF>();
		}
		//System.out.println(simCounter);
		
		//System.out.println(performanceRecords.get(bestI).evaluatingAction);
		//for(Performance perf : performanceRecords){
		//	System.out.println(perf.tryNumber + " " + perf.accum_performance + " " + perf.accum_performance / perf.tryNumber);
		//}
		System.out.println("Best performance is: " + performanceRecords.get(bestI).accum_performance / performanceRecords.get(bestI).tryNumber);
		return performanceRecords.get(bestI).evaluatingAction;
	}
	
	public ArrayList<ArrayList<PVAR_INST_DEF>> findAllPossibleActions(State s) throws EvalException{
		//int count = 0;
		ArrayList<ArrayList<PVAR_INST_DEF>> finalActions = new ArrayList<ArrayList<PVAR_INST_DEF>>();
		boolean passed_constraints = false;
		for(PVAR_NAME actionName : s._alActionNames){
			ArrayList<ArrayList<LCONST>> terms = s.generateAtoms(actionName);
			for(ArrayList<LCONST> term : terms){
				ArrayList<PVAR_INST_DEF> singleAction = new ArrayList<PVAR_INST_DEF>();
				PVAR_INST_DEF theSingleAction = new PVAR_INST_DEF(actionName._sPVarName, true, term);
				singleAction.add(theSingleAction);
				passed_constraints = true;
    			if(passed_constraints){
    				try {
    					s.checkStateActionConstraints(singleAction);
    				} catch (EvalException e) { 
    					// Got an eval exception, constraint violated
    					passed_constraints = false;
    				}
    			}
				if( passed_constraints ){
					finalActions.add(singleAction);
				}
			}
		}
		
		
		
		if(s._nMaxNondefActions > 1){
			//put them into array
			PVAR_INST_DEF arraySigAct[] = new PVAR_INST_DEF[finalActions.size()];
			for(int i = 0; i < finalActions.size(); i ++ ){
				arraySigAct[i] = finalActions.get(i).get(0);
			}
			
			//find all possible combinations
			ArrayList<List<PVAR_INST_DEF[]>> actionList = new ArrayList<List<PVAR_INST_DEF[]>>();
			for(int m = 1; m <= s._nMaxNondefActions; m ++){  
				AssemblyDemo c = new AssemblyDemo();
		        actionList.add(c.combination(arraySigAct, m));
			}
			
			//check availability of combinatorial actions
			//add availability to single action involved
	        for(int i = 1; i < s._nMaxNondefActions; i ++){
	        	List<PVAR_INST_DEF[]> list = actionList.get(i);
	        	for(int j = 0; j < list.size(); j ++){
	        		//count ++;
	        		PVAR_INST_DEF[] caa = list.get(j);
	        		ArrayList<PVAR_INST_DEF> combinatorialAction = new ArrayList<PVAR_INST_DEF>();
	        		for(int t = 0; t < caa.length; t ++){
	        			combinatorialAction.add(caa[t]);
	        		}
	        		passed_constraints = true;
	    			if(passed_constraints){
	    				try {
	    					s.checkStateActionConstraints(combinatorialAction);
	    				} catch (EvalException e) { 
	    					// Got an eval exception, constraint violated
	    					passed_constraints = false;
	    				}
	    			}
	        		if(passed_constraints){
	        			finalActions.add(combinatorialAction);
	        		}
	        	}
	        }
	       // int a = 1;
		}
		finalActions.add(new ArrayList<RDDL.PVAR_INST_DEF>());
		return finalActions;
	}
	
	public boolean IfGenerateALL(State s, INSTANCE instance, DOMAIN domain) throws EvalException{
		//initialize
		long t0 = System.currentTimeMillis();
		double accum_reward = 0.0d;
		double cur_discount = 1.0d;
		int h = 0;
		
		ArrayList<ArrayList<PVAR_INST_DEF>> possibleFirstLevelAct = null;
		int numOfTopAct = 0;
		//if have checked all possible action at top level
		//just quit
		//if not generate all this var will not be used
		boolean ifCheckAll = false;
		boolean ifDirectlySearch = false;
		int numOfAction = 0;
		int endingPoint[] = null;
		double combNumEnding[] = null;
		RandomConcurrentPolicyIndex randomConcreteGen = null;
		HashMap<ArrayList<Integer>, Boolean> already = null;	
		
		//no matter what we need to get ready for generate random action
		//preparation before generate random action
		numOfAction = s._alActionNames.size();
		endingPoint = new int[numOfAction];
		PVAR_NAME actionName[] = new PVAR_NAME[numOfAction];
		int end = -1;
		ArrayList<ArrayList<ArrayList<LCONST>>> terms = new ArrayList<ArrayList<ArrayList<LCONST>>>();
		for(int i = 0; i < numOfAction; i ++){
			PVAR_NAME p = s._alActionNames.get(i);
			actionName[i] = p;
			ArrayList<ArrayList<LCONST>> term = s.generateAtoms(p);
			terms.add(s.generateAtoms(p));
			end += term.size();
			endingPoint[i] = end;
		}
		
		//with what porb we choose the number of actions participating into a comb
		combNumEnding = new double[s._nMaxNondefActions+1];
		combNumEnding[0] = 1;
		int numOfsingleAction = endingPoint[numOfAction-1] + 1;
		for(int m = 1; m <= s._nMaxNondefActions; m ++){
			//cal how many m-combs exist
			double temp = 1;
			for(int i = 0; i < m; i ++){
				temp *= (numOfsingleAction - i);
			}
			for(int i = 2; i <= m; i ++){
				temp /= i;
			}
			combNumEnding[m] = combNumEnding[m-1] + temp;
		}
		for(int m = 0; m <= s._nMaxNondefActions; m ++){
			combNumEnding[m] /= combNumEnding[s._nMaxNondefActions];
		}
		
		//tempState
		AState as = new AState();
		as.init(s);
		
		//store the first level actions
		ArrayList<PVAR_INST_DEF> _firstLevelAcs = new ArrayList<PVAR_INST_DEF>();
		
		//used to record the action at each step
		ArrayList<PVAR_INST_DEF> _randomAction = new ArrayList<PVAR_INST_DEF>();
		RandomConcurrentPolicyIndex _actionGenerator = new RandomConcurrentPolicyIndex();
		
		for( ; h < instance._nHorizon * searchRatio && currentRound + h <= instance._nHorizon; h++ ) {
			
			HashMap<ArrayList<Integer>, Boolean> tempAlready = new HashMap<ArrayList<Integer>, Boolean>();
			_randomAction = _actionGenerator.getActions(as, tempAlready, endingPoint, combNumEnding);
			//compute next state
			//System.out.println(as._state);
			
			as.computeNextState(_randomAction, _random);
			
			//System.out.println(as._nextState);
			
			//compute reward
			/*
			if(h == 2){
				System.out.println(_firstLevelAcs);
				System.out.println(as._state);
			}
			*/
			double reward = ((Number)domain._exprReward.sample(new HashMap<LVAR,LCONST>(), 
				as, _random)).doubleValue();
			accum_reward += reward * cur_discount;
			cur_discount *= instance._dDiscount;
			as.advanceNextState();
		}
		long t = System.currentTimeMillis();
		double possibleRuns = Math.ceil(_timeAllowed / (t - t0));
		int numSingleAction = 0;
		for(PVAR_NAME p : s._alActionNames){
			ArrayList<ArrayList<LCONST>> term = s.generateAtoms(p);
			numSingleAction += term.size();
		}
		possibleComb = 0;
		for(int m = 1; m <= s._nMaxNondefActions; m ++){
			//cal how many m-combs exist
			double temp = 1;
			for(int i = 0; i < m; i ++){
				temp *= (numSingleAction - i);
			}
			for(int i = 2; i <= m; i ++){
				temp /= i;
			}
			possibleComb += temp;
		}
		possibleComb ++;
		if(ifPrint){
			System.out.println("Estimated possible runs: " + possibleRuns);
			System.out.println("How many possile combs: " + possibleComb);
		}
		
		if(possibleRuns * ratioOfJudgment <= possibleComb || possibleComb > genAllThreshold){
			return false;
		}
		else{
			return true;
		}
	}
}


