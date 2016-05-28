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
import rddl.RDDL.DOMAIN;
import rddl.RDDL.INSTANCE;
import rddl.RDDL.ENUM_TYPE_DEF;
import rddl.RDDL.LCONST;
import rddl.RDDL.LVAR;
import rddl.RDDL.PVARIABLE_DEF;
import rddl.RDDL.PVAR_INST_DEF;
import rddl.RDDL.PVAR_NAME;
import util.Permutation;

public class NNNR03 extends Policy {

	public int NUM_CONCURRENT_ACTIONS = 2; // Max number of non-default concurrent actions
	public int MAX_INT_VALUE = 5; // Max int value to use when selecting random action
	public double MAX_REAL_VALUE = 5.0d; // Max real value to use when selecting random action
	public int POSSIBLE_ACTIONS = 1000;  //max number of possible actions
	public int mode = 1; //1 for time 2 for number
	public int NUM_OF_ROLLOUT = 1000;
	double ipsino = 0.5f;
	double searchRatio = 0.5;
	double ratioOfJudgment = 20;
	long genAllThreshold = 40000;
	double possibleComb = 0;
	
	
	public class Performance{			//record performance of each action
		public Performance(){
			accum_performance = 0;
			tryNumber = 0;
		}
		public Performance(double acc, int num, double val, ArrayList<PVAR_INST_DEF> act){
			accum_performance = acc;
			value = val;
			tryNumber = num;
			evaluatingAction = act;
		}
		public ArrayList<PVAR_INST_DEF> evaluatingAction;
		public double accum_performance;
		public int tryNumber;
		public double value;
	};
	
	public NNNR03 () { 
		super();
	}
	
	public NNNR03(String instance_name) {
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
	
	//after top level action have been tried at least once
	//choose action ipsino-grredily based on current performance
	//return the index of the action out of the performance list
	int ChooseTopActWithIpsi(ArrayList<Performance> perfRec, int bestI){
		int index;
		double dice = _random.nextDouble();
		if(dice > ipsino){
			index = bestI;
		}
		else{
			index = _random.nextInt(perfRec.size());
		}
		return index;
	}
	
	
	
	public ArrayList<PVAR_INST_DEF> getActions(State s) throws EvalException {
	
		
		//get the damin and parameters
		INSTANCE instance = rddl._tmInstanceNodes.get(_sInstanceName);
		DOMAIN domain = rddl._tmDomainNodes.get(instance._sDomain);
		NUM_CONCURRENT_ACTIONS = instance._nNonDefActions;
		
		/********************needs modification ************************/
		ArrayList<Performance> performanceRecords = new ArrayList<Performance>();
		int recordsCounter = 0;
		/********************needs modification ************************/
		
		//count the times of simulation
		long t0 = System.currentTimeMillis();
		
		//how many simulations have been executed
		long simCounter = 0;
		
		//record which one is the current best
		int bestI = -1;
		
		
		possibleComb = 0;
		
		//check if generate all actions
		//this is a complex computation which can be set with different parameters
		
		boolean ifGenerateAll = IfGenerateALL(s, instance, domain);
		ArrayList<ArrayList<PVAR_INST_DEF>> possibleFirstLevelAct = null;
		int numOfTopAct = 0;
		//if have checked all possible action at top level
		//just quit
		//if not generate all this var will not be used
		boolean ifCheckAll = false;
		int numOfAction = 0;
		RandomConcurrentPolicyIndex randomConcreteGen = new RandomConcurrentPolicyIndex(s);
		
		if(ifGenerateAll){
			//generate all actions
			//this might be dangero
			System.out.println("Generate all actions! This might be dangerous!");
			possibleFirstLevelAct = findAllPossibleActions(s);
			numOfTopAct = possibleFirstLevelAct.size();
			Collections.shuffle(possibleFirstLevelAct);
		}
		
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
			State cs = new State();
			cs = (State) DeepCloneUtil.deepClone(s);
			
			
			//store the first level actions
			ArrayList<PVAR_INST_DEF> _firstLevelAcs = new ArrayList<PVAR_INST_DEF>();
			
			//used to record the action at each step
			ArrayList<PVAR_INST_DEF> _randomAction = new ArrayList<PVAR_INST_DEF>();
			
			//the index of currently tried root action
			//index works on performance list
			//only used after each of root actions has beed tried at least once
			int index = -1;
			
			//simulate once
			for( ; h < instance._nHorizon * searchRatio && currentRound + h <= instance._nHorizon; h++ ) {
				//deal with top action generation and selection
				if(h == 0){
					if(ifGenerateAll){
						if(simCounter> possibleFirstLevelAct.size()){
							index = ChooseTopActWithIpsi(performanceRecords, bestI);
							_randomAction = performanceRecords.get(index).evaluatingAction;
						}
						else{
							_randomAction = possibleFirstLevelAct.get((int)simCounter - 1);
							//System.out.println(_randomAction);
						}
					}
					else{
						_randomAction = randomConcreteGen.getCAction(s);
						if(randomConcreteGen.already.size() == possibleComb){
							//possibly that no real actions are generated this time
							if(_randomAction.size() == 1 && _randomAction.get(0)._oValue.equals(false)){
								index = ChooseTopActWithIpsi(performanceRecords, bestI);
								_randomAction = performanceRecords.get(index).evaluatingAction;
							}
						}
						//it's possible that this time we don't generate any action
						//arbitarily get the first action
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
				else{
				
					//ANoopPolicy noop = new ANoopPolicy();
					//_randomAction = noop.getActions(as);
					RandomConcurrentPolicyIndex _actionGenerator = new RandomConcurrentPolicyIndex(cs);
					_randomAction = _actionGenerator.getCActionDup(cs);
					//System.out.println(_randomAction);
				}
				
				//record first level action if h == 0
				if( h == 0){
					_firstLevelAcs = _randomAction;
				}
				
				//compute next state
				//System.out.println(as._state);
				
				cs.computeNextState(_randomAction, _random);
				
				//System.out.println(as._nextState);
				
				//compute reward
				/*
				if(h == 2){
					System.out.println(_firstLevelAcs);
					System.out.println(as._state);
				}
				*/
				double reward = ((Number)domain._exprReward.sample(new HashMap<LVAR,LCONST>(), 
					cs, _random)).doubleValue();
				accum_reward += reward * cur_discount;
				cur_discount *= instance._dDiscount;
				cs.advanceNextState();
			}
			//System.out.println(simCounter + " " + _firstLevelAcs + " " + accum_reward);
			
			//add performance to records
			//record performance
			
			//not search each root action yet, so just add performance to the list
			if(index == -1){

				performanceRecords.add(new Performance(accum_reward, 1, accum_reward, _firstLevelAcs));
				if(bestI == -1 || accum_reward > performanceRecords.get(bestI).value){
					bestI = performanceRecords.size() - 1;
				}
			}
			//if already searched all actions
			//update the bestI when needed
			else{
				//this variable may not be used if index != bestI
				double oldBest = -100000000.0;
				if(index == bestI){
					//record the old best value
					oldBest = performanceRecords.get(index).value;
				}
				performanceRecords.get(index).tryNumber ++;
				performanceRecords.get(index).accum_performance += accum_reward;
				double newValue = performanceRecords.get(index).accum_performance / performanceRecords.get(index).tryNumber;
				performanceRecords.get(index).value = newValue;
				if(index != bestI && newValue > performanceRecords.get(bestI).value){
					bestI = index;
				}
				if(index == bestI && newValue < oldBest){
					//consider if any other performance is better
					for(Performance p: performanceRecords){
						if(p.value > oldBest){
							oldBest = p.value;
							bestI = performanceRecords.indexOf(p);
						}
					}
				}
			}
		}
		if(ifPrint){
			for(Performance p: performanceRecords){
				System.out.println(p.evaluatingAction + " " + p.tryNumber + " " + p.value);
			}
		}
//		actions = new RandomConcurrentPolicy().getActions(s);
		if(bestI == -1){
			return new ArrayList<RDDL.PVAR_INST_DEF>();
		}
		System.out.println(simCounter);
		
		//System.out.println(performanceRecords.get(bestI).evaluatingAction);
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
		
		//tempState
		State cs = new State();
		cs = (State) DeepCloneUtil.deepClone(s);
		
		//store the first level actions
		ArrayList<PVAR_INST_DEF> _firstLevelAcs = new ArrayList<PVAR_INST_DEF>();
		
		//used to record the action at each step
		ArrayList<PVAR_INST_DEF> _randomAction = new ArrayList<PVAR_INST_DEF>();
		RandomConcurrentPolicyIndex _actionGenerator = new RandomConcurrentPolicyIndex(cs);
		
		
		for( ; h < instance._nHorizon * searchRatio && currentRound + h <= instance._nHorizon; h++ ) {
			
			_randomAction = _actionGenerator.getCAction(cs);
			//compute next state
			//System.out.println(as._state);
			
			cs.computeNextState(_randomAction, _random);
			
			//System.out.println(as._nextState);
			
			//compute reward
			/*
			if(h == 2){
				System.out.println(_firstLevelAcs);
				System.out.println(as._state);
			}
			*/
			double reward = ((Number)domain._exprReward.sample(new HashMap<LVAR,LCONST>(), 
				cs, _random)).doubleValue();
			accum_reward += reward * cur_discount;
			cur_discount *= instance._dDiscount;
			cs.advanceNextState();
		}
		long t = System.currentTimeMillis();
		double possibleRuns = Math.ceil(_timeAllowed / (t - t0));
		int numSingleAction = 0;
		for(PVAR_NAME p : s._alActionNames){
			ArrayList<ArrayList<LCONST>> term = s.generateAtoms(p);
			numSingleAction += term.size();
		}
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


