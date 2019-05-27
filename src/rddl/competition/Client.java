/**
 * RDDL: Main client code for interaction with RDDLSim server
 * 
 * @author Sungwook Yoon (sungwook.yoon@gmail.com)
 * @version 10/1/10
 *
 **/

package rddl.competition;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.lang.reflect.InvocationTargetException;
import java.net.InetAddress;
import java.net.Socket;
import java.text.DecimalFormat;
import java.util.ArrayList;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.apache.xerces.impl.dv.util.Base64;
import org.apache.xerces.parsers.DOMParser;
import org.apache.xml.serialize.OutputFormat;
import org.apache.xml.serialize.XMLSerializer;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.w3c.dom.Text;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

import rddl.EvalException;
import rddl.RDDL;
import rddl.RDDL.DOMAIN;
import rddl.RDDL.IF_EXPR;
import rddl.RDDL.INSTANCE;
import rddl.RDDL.LCONST;
import rddl.RDDL.NONFLUENTS;
import rddl.RDDL.PVAR_INST_DEF;
import rddl.RDDL.PVAR_NAME;
import rddl.State;
import rddl.parser.ParseException;
import rddl.parser.parser;
import rddl.policy.Policy;
import rddl.policy.RandomEnumPolicy;
import rddl.viz.StateViz;
/** The SocketClient class is a simple example of a TCP/IP Socket Client.
 *
 */

public class Client {
	
	public static final boolean SHOW_XML = false;
	public static final boolean SHOW_MSG = false;
	public static final boolean SHOW_MEMORY_USAGE = true;
	public static final Runtime RUNTIME = Runtime.getRuntime();
	public static final int DEFAULT_RANDOM_SEED = 0;
	private static DecimalFormat _df = new DecimalFormat("0.##");	
	enum XMLType {
		ROUND,TURN,ROUND_END,END_TEST,NONAME
	}

	private static RDDL rddl = new RDDL();

	static int numRounds;
	static double timeAllowed;
	static int curRound;
	double reward;
	static int roundsLeft;
	static int turnLeft;
	int id;
	
	

	Client () {
		numRounds = 0;
		timeAllowed = 0;
		curRound = 0;
		reward = 0;
		id = 0;
	}
	
	/**
	 * 
	 * @param args
	 * 1. rddl description file name with RDDL syntax, with complete path (sysadmin.rddl)
	 * 2. instance name in rddl / directory of rddl files
	 * 3. host name (local host)
	 * 4. client name (for record keeping purpose on server side. identify yourself with name.
	 * 5. (optional) port number
	 * 6. (optional) random seed
	 * @throws IOException 
	 * @throws RDDLXMLException 
	 * @throws ClassNotFoundException 
	 * @throws SecurityException 
	 * @throws NoSuchMethodException 
	 * @throws InvocationTargetException 
	 * @throws IllegalArgumentException 
	 * @throws IllegalAccessException 
	 * @throws InstantiationException 
	 * @throws EvalException 
	 */
	
	public static void RunWithRatio(State state, INSTANCE instance, NONFLUENTS nonFluents, DOMAIN domain, 
			InputSource isrc, Client client, OutputStreamWriter osw, String msg, Policy policy, Class c, BufferedInputStream isr,
			DOMParser p, String instanceName) throws IOException, RDDLXMLException, ClassNotFoundException, InstantiationException, IllegalAccessException, IllegalArgumentException, InvocationTargetException, NoSuchMethodException, SecurityException, EvalException {
		int r = 0;
		int testingNum = 20;
		//number of rounds as sum of original rounds and testing rounds
		long totalRounds = Client.numRounds + testingNum;
		long totalStepLeft = totalRounds * instance._nHorizon;
		long totalStepUsed = 0;
		double totalTimeUsage = 0;
		//find the ratios for depth testing
		double[] possibleRatio = Policy.DefinePossibleRatio(testingNum);
		int possibleIndex = -1;
		double avgTotalReward = 0;
		double maxAvgReward = -Double.MAX_VALUE;
		double bestRatio = -1;
		Policy.avgUpdates = 0;
		Policy.avgVarDepth = 0;
		Policy.avgSearchDepth = 0;
		Policy.theRatio = 0.0;
		Policy.effectiveSteps = 0;
		for( ; r < totalRounds; r++ ) {
			if(r < 3 * possibleRatio.length){
				if(r % 3 == 0){
					avgTotalReward /= 3;
					if(r != 0){
						System.out.println("testing: " + Policy.theRatio + " = " + avgTotalReward);
						Policy.avgVarDepth /= Policy.effectiveSteps;
						Policy.avgUpdates /= Policy.effectiveSteps;
						Policy.avgSearchDepth /= Policy.effectiveSteps;
						System.out.println("Average var depth: " + Policy.avgVarDepth);
						System.out.println("Average search depth: " + Policy.avgSearchDepth);
						System.out.println("Average updates: " + Policy.avgUpdates);
						if(avgTotalReward > maxAvgReward){
							maxAvgReward = avgTotalReward;
							bestRatio = Policy.theRatio;
						}
					}
					avgTotalReward = 0;
					Policy.avgVarDepth = 0;
					Policy.avgUpdates = 0;
					Policy.avgSearchDepth = 0;
					Policy.effectiveSteps = 0;
					possibleIndex ++;
					Policy.theRatio = possibleRatio[possibleIndex];
				}
			}
			if(r == testingNum){
				Policy.theRatio = bestRatio;
				Policy.ifReallyRun = true;
				System.out.println("Decide to use ratio: " + Policy.theRatio);
			}
			
			if (SHOW_MEMORY_USAGE)
				System.out.print("[ Memory usage: " + 
						_df.format((RUNTIME.totalMemory() - RUNTIME.freeMemory())/1e6d) + "Mb / " + 
						_df.format(RUNTIME.totalMemory()/1e6d) + "Mb" + 
						" = " + _df.format(((double) (RUNTIME.totalMemory() - RUNTIME.freeMemory()) / 
										   (double) RUNTIME.totalMemory())) + " ]\n");
			
			state.init(domain._hmObjects, nonFluents != null ? nonFluents._hmObjects : null, instance._hmObjects,
					domain._hmTypes, domain._hmPVariables, domain._hmCPF,
					instance._alInitState, nonFluents == null ? new ArrayList<PVAR_INST_DEF>() : nonFluents._alNonFluents, instance._alNonFluents,
					domain._alStateConstraints, domain._alActionPreconditions, domain._alStateInvariants,  
					domain._exprReward, instance._nNonDefActions);
					
			msg = createXMLRoundRequest(r >= testingNum);
			Server.sendOneMessage(osw, msg);
			isrc = Server.readOneMessage(isr);
			processXMLRoundInit(p, isrc, r+1);
			
			if ( timeAllowed < 0 ) {
				break;
			} // TODO
			int h =0;
			//System.out.println(instance._nHorizon);
			boolean round_ended_early = false;
			for(; h < instance._nHorizon; h++ ) {
				if (SHOW_MSG) System.out.println("Reading turn message");
				isrc = Server.readOneMessage(isr);
				Element e = parseMessage(p, isrc);
				round_ended_early = e.getNodeName().equals(Server.ROUND_END);
				if (round_ended_early)
					break;
				if (SHOW_MSG) System.out.println("Done reading turn message");
				//if (SHOW_XML)
				//	Server.printXMLNode(e); // DEBUG
				ArrayList<PVAR_INST_DEF> obs = processXMLTurn(e,state);
				
				//time allowed is deducted by 3 seconds to avoid time issue
				timeAllowed -= 3000;
				
				//calculate total time for this step
				double timeForStep = timeAllowed / totalStepLeft;
				
				//calculate avg time usage
				//if the avg time usage is too long to complete the step
				//simply do random
				totalTimeUsage += timeForStep;
				totalStepUsed ++;
				if(totalTimeUsage / totalStepUsed > timeAllowed){
					System.out.println("Time left is not sufficient to do one step; Change to Random Policy!!");
					c = Class.forName("rddl.policy.RandomConcurrentPolicyIndex");
					policy = (Policy)c.getConstructor(
							new Class[]{String.class}).newInstance(new Object[]{instanceName});
				}
				
				if (SHOW_MSG) System.out.println("Done parsing turn message");
				if ( obs == null ) {
					if (SHOW_MSG) System.out.println("No state/observations received.");
					if (SHOW_XML)
						Server.printXMLNode(p.getDocument()); // DEBUG
				} else if (domain._bPartiallyObserved) {
					state.clearPVariables(state._observ);
					state.setPVariables(state._observ, obs);
				} else {
					state.clearPVariables(state._state);
					state.setPVariables(state._state, obs);
				}
				policy.setCurrentRound(h);
				policy.setRddlDomain(rddl);
				policy.setTimeAllowed(new Double(timeForStep).longValue());
				if(Policy.ifReallyRun){
					System.out.println("Steps left: " + totalStepLeft);
					System.out.println("Time allowed for this step: " + timeForStep);
				}
				
				ArrayList<PVAR_INST_DEF> actions = 
					policy.getActions(obs == null ? null : state);
				msg = createXMLAction(actions);
				if (SHOW_MSG)
					System.out.println("Sending: " + msg);
				Server.sendOneMessage(osw, msg);
				
				totalStepLeft --;
			}
			if ( h < instance._nHorizon ) {
				break;
			}
			if (!round_ended_early) // otherwise isrc is the round-end message
				isrc = Server.readOneMessage(isr);
			Element round_end_msg = parseMessage(p, isrc);
			double reward = processXMLRoundEnd(round_end_msg);
			if(Policy.ifReallyRun){
				policy.roundEnd(reward);
			}
			
			avgTotalReward += reward;
			//System.out.println("Round reward: " + reward);
			
			if (getTimeLeft(round_end_msg) <= 0l)
				break;
		}
		isrc = Server.readOneMessage(isr);
		double total_reward = processXMLSessionEnd(p, isrc);
		policy.sessionEnd(total_reward);
	}
	
	public static void Run(State state, INSTANCE instance, NONFLUENTS nonFluents, DOMAIN domain, 
			InputSource isrc, Client client, OutputStreamWriter osw, String msg, Policy policy, Class c, BufferedInputStream isr,
			DOMParser p, String instanceName) throws IOException, RDDLXMLException, ClassNotFoundException, InstantiationException, IllegalAccessException, IllegalArgumentException, InvocationTargetException, NoSuchMethodException, SecurityException, EvalException {
		int r = 0;
		//number of rounds as sum of original rounds and testing rounds
		long totalRounds = Client.numRounds;
		long totalStepLeft = totalRounds * instance._nHorizon;
		long totalStepUsed = 0;
		double totalTimeUsage = 0;

		for( ; r < totalRounds; r++ ) {
			if (SHOW_MEMORY_USAGE)
				System.out.print("[ Memory usage: " + 
						_df.format((RUNTIME.totalMemory() - RUNTIME.freeMemory())/1e6d) + "Mb / " + 
						_df.format(RUNTIME.totalMemory()/1e6d) + "Mb" + 
						" = " + _df.format(((double) (RUNTIME.totalMemory() - RUNTIME.freeMemory()) / 
										   (double) RUNTIME.totalMemory())) + " ]\n");
			
			state.init(domain._hmObjects, nonFluents != null ? nonFluents._hmObjects : null, instance._hmObjects,
					domain._hmTypes, domain._hmPVariables, domain._hmCPF,
					instance._alInitState, nonFluents == null ? new ArrayList<PVAR_INST_DEF>() : nonFluents._alNonFluents, instance._alNonFluents,
					domain._alStateConstraints, domain._alActionPreconditions, domain._alStateInvariants,  
					domain._exprReward, instance._nNonDefActions);
					
			msg = createXMLRoundRequest(true);
			Server.sendOneMessage(osw, msg);
			isrc = Server.readOneMessage(isr);
			processXMLRoundInit(p, isrc, r+1);
			
			if ( timeAllowed < 0 ) {
				break;
			} // TODO
			int h =0;
			//System.out.println(instance._nHorizon);
			boolean round_ended_early = false;
			for(; h < instance._nHorizon; h++ ) {
				if (SHOW_MSG) System.out.println("Reading turn message");
				isrc = Server.readOneMessage(isr);
				Element e = parseMessage(p, isrc);
				round_ended_early = e.getNodeName().equals(Server.ROUND_END);
				if (round_ended_early)
					break;
				if (SHOW_MSG) System.out.println("Done reading turn message");
				//if (SHOW_XML)
				//	Server.printXMLNode(e); // DEBUG
				ArrayList<PVAR_INST_DEF> obs = processXMLTurn(e,state);
				
				//time allowed is deducted by 3 seconds to avoid time issue
				timeAllowed -= 3000;
				
				//calculate total time for this step
				double timeForStep = timeAllowed / totalStepLeft;
				
				//calculate avg time usage
				//if the avg time usage is too long to complete the step
				//simply do random
				totalTimeUsage += timeForStep;
				totalStepUsed ++;
				if(totalTimeUsage / totalStepUsed > timeAllowed){
					System.out.println("Time left is not sufficient to do one step; Change to Random Policy!!");
					c = Class.forName("rddl.policy.RandomConcurrentPolicyIndex");
					policy = (Policy)c.getConstructor(
							new Class[]{String.class}).newInstance(new Object[]{instanceName});
				}
				
				if (SHOW_MSG) System.out.println("Done parsing turn message");
				if ( obs == null ) {
					if (SHOW_MSG) System.out.println("No state/observations received.");
					if (SHOW_XML)
						Server.printXMLNode(p.getDocument()); // DEBUG
				} else if (domain._bPartiallyObserved) {
					state.clearPVariables(state._observ);
					state.setPVariables(state._observ, obs);
				} else {
					state.clearPVariables(state._state);
					state.setPVariables(state._state, obs);
				}
				policy.setCurrentRound(h);
				policy.setRddlDomain(rddl);
				policy.setTimeAllowed(new Double(timeForStep).longValue());
				if(Policy.ifReallyRun){
					System.out.println("Steps left: " + totalStepLeft);
					System.out.println("Time allowed for this step: " + timeForStep);
				}
				
				ArrayList<PVAR_INST_DEF> actions = 
					policy.getActions(obs == null ? null : state);
				msg = createXMLAction(actions);
				if (SHOW_MSG)
					System.out.println("Sending: " + msg);
				Server.sendOneMessage(osw, msg);
				
				totalStepLeft --;
			}
			if ( h < instance._nHorizon ) {
				break;
			}
			if (!round_ended_early) // otherwise isrc is the round-end message
				isrc = Server.readOneMessage(isr);
			Element round_end_msg = parseMessage(p, isrc);
			double reward = processXMLRoundEnd(round_end_msg);
			if(Policy.ifReallyRun){
				policy.roundEnd(reward);
			}
			
			//System.out.println("Round reward: " + reward);
			if (getTimeLeft(round_end_msg) <= 0l)
				break;
		}
		isrc = Server.readOneMessage(isr);
		double total_reward = processXMLSessionEnd(p, isrc);
		policy.sessionEnd(total_reward);
	}
	
	
	public static void main(String[] args) {

		/** Define a host server */
		String host = "localhost";
		/** Define a port */
		int port = Server.PORT_NUMBER;
		String clientName = "SOGBOFA";
		String instanceName = null;
		int randomSeed = DEFAULT_RANDOM_SEED;
		
		State      state;
		INSTANCE   instance;
		NONFLUENTS nonFluents = null;
		DOMAIN     domain;
		StateViz   stateViz;
		
		StringBuffer instr = new StringBuffer();

		try {

			// get all parameters
			instanceName = args[0];
			port = Integer.valueOf(args[1]);
			
			
			//connect to the server
			//get back the content of the rddl files
			//get rddl
			/** Obtain an address object of the server */
			InetAddress address = InetAddress.getByName(host);
			/** Establish a socket connetion */
			Socket connection = new Socket(address, port);
			System.out.println("RDDL client initialized");
			
			/** Instantiate a BufferedOutputStream object */
			BufferedOutputStream bos = new BufferedOutputStream(connection.
					getOutputStream());
			/** Instantiate an OutputStreamWriter object with the optional character
			 * encoding.
			 */
			OutputStreamWriter osw = new OutputStreamWriter(bos, "US-ASCII");
			/** Write across the socket connection and flush the buffer */
			String msg = createXMLSessionRequest(instanceName, clientName);
			Server.sendOneMessage(osw, msg);
			BufferedInputStream isr = new BufferedInputStream(connection.getInputStream());
			/**Instantiate an InputStreamReader with the optional
			 * character encoding.
			 */
			//InputStreamReader isr = new InputStreamReader(bis, "US-ASCII");
			DOMParser p = new DOMParser();
			
			/**Read the socket's InputStream and append to a StringBuffer */
			InputSource isrc = Server.readOneMessage(isr);
			Client client = processXMLSessionInit(p, isrc, instanceName);
			
			System.out.println(client.id + ":" + client.numRounds);
			System.out.println("Total time allowed: " + client.timeAllowed);

			VisCounter visCounter = new VisCounter();
			
			// Cannot assume always in rddl.policy
			Class c = Class.forName("rddl.policy.RevAccGradient");
				
			//prepare for planning
			state = new State();
			
			// Note: following constructor approach suggested by Alan Olsen
			Policy policy = (Policy)c.getConstructor(
					new Class[]{String.class}).newInstance(new Object[]{instanceName});
			//policy.setRDDL(rddl);
			policy.setRandSeed(randomSeed);
			policy.setVisCounter(visCounter);

			
			instance = rddl._tmInstanceNodes.get(instanceName);
			
			if (instance._sNonFluents != null) {
				nonFluents = rddl._tmNonFluentNodes.get(instance._sNonFluents);
			}
			
			domain = rddl._tmDomainNodes.get(instance._sDomain);
			if (nonFluents != null && !instance._sDomain.equals(nonFluents._sDomain)) {
				System.err.println("Domain name of instance and fluents do not match: " + 
							instance._sDomain + " vs. " + nonFluents._sDomain);
				System.exit(1);
			}
			
			state.init(domain._hmObjects, nonFluents != null ? nonFluents._hmObjects : null, instance._hmObjects,
					domain._hmTypes, domain._hmPVariables, domain._hmCPF,
					instance._alInitState, nonFluents == null ? new ArrayList<PVAR_INST_DEF>() : nonFluents._alNonFluents, instance._alNonFluents,
					domain._alStateConstraints, domain._alActionPreconditions, domain._alStateInvariants, 
					domain._exprReward, instance._nNonDefActions);
			
			// If necessary, correct the partially observed flag since this flag determines what content will be seen by the Client
			if ((domain._bPartiallyObserved && state._alObservNames.size() == 0)
					|| (!domain._bPartiallyObserved && state._alObservNames.size() > 0)) {
				boolean observations_present = (state._alObservNames.size() > 0);
				System.err.println("WARNING: Domain '" + domain._sDomainName
								+ "' partially observed (PO) flag and presence of observations mismatched.\nSetting PO flag = " + observations_present + ".");
				domain._bPartiallyObserved = observations_present;
			}

			// Not strictly enforcing flags anymore... 
			//if ((domain._bPartiallyObserved && state._alObservNames.size() == 0)
			//		|| (!domain._bPartiallyObserved && state._alObservNames.size() > 0)) {
			//	System.err.println("Domain '" + domain._sDomainName + "' partially observed flag and presence of observations mismatched.");
			//}
			policy.setInstance(instanceName);
			policy.setVisCounter(visCounter);

			                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     
			
			
			/** Close the socket connection. */
			connection.close();
			System.out.println(instr);
		}
		catch (Exception g) {
			System.out.println("Exception: " + g);
			g.printStackTrace();
		}
	}
	
	static Element parseMessage(DOMParser p, InputSource isrc) throws RDDLXMLException {
		try {
			p.parse(isrc);
		} catch (SAXException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
			// Debug info to explain parse error
			//Server.showInputSource(isrc);
			throw new RDDLXMLException("sax exception");
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
			throw new RDDLXMLException("io exception");
		}
		if (SHOW_XML)
			Server.printXMLNode(p.getDocument()); // DEBUG

		return p.getDocument().getDocumentElement();
	}
	
	static String serialize(Document dom) {
		OutputFormat format = new OutputFormat(dom);
//		format.setIndenting(true);
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		
		XMLSerializer xmls = new XMLSerializer(baos, format);
		try {
			xmls.serialize(dom);
			return baos.toString();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}
	
	static XMLType getXMLType(DOMParser p,InputSource isrc) {
		Element e = p.getDocument().getDocumentElement();
		if ( e.getNodeName().equals("turn") ) {
			return XMLType.TURN;
		} else if (e.getNodeName().equals("round")) {
			return XMLType.ROUND;
		} else if (e.getNodeName().equals("round-end")) {
			return XMLType.ROUND_END;
		} else if (e.getNodeName().equals("end-test")) {
			return XMLType.END_TEST;
		} else {
			return XMLType.NONAME;
		}
	}
	
	static String createXMLSessionRequest (String problemName, String clientName) {
		DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
		try {
			//get an instance of builder
			DocumentBuilder db = dbf.newDocumentBuilder();

			//create an instance of DOM
			Document dom = db.newDocument();
			Element rootEle = dom.createElement(Server.SESSION_REQUEST);
			dom.appendChild(rootEle);
			Server.addOneText(dom, rootEle, Server.CLIENT_NAME, clientName);
			Server.addOneText(dom, rootEle, Server.PROBLEM_NAME, problemName);
			Server.addOneText(dom, rootEle, Server.INPUT_LANGUAGE, "rddl");
			return serialize(dom);
		} catch (Exception e) {
			return null;
		}
	}
	
	static String createXMLRoundRequest(boolean ifExcutePolicy) {
		DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
		try {
			DocumentBuilder db = dbf.newDocumentBuilder();
			Document dom = db.newDocument();
			Element rootEle = dom.createElement(Server.ROUND_REQUEST);
			dom.appendChild(rootEle);
			Server.addOneText(dom, rootEle, Server.EXECUTE_POLICY, ifExcutePolicy ? "yes" : "no");
			return serialize(dom);
		} catch (Exception e) {
			return null;
		}
	}
	
	static Client processXMLSessionInit(DOMParser p, InputSource isrc, String instanceName) throws RDDLXMLException {
		try {
			p.parse(isrc);
		} catch (SAXException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
			throw new RDDLXMLException("sax exception");
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
			throw new RDDLXMLException("io exception");
		}
		Client c = new Client();
		Element e = p.getDocument().getDocumentElement();
		byte[] rddlDesc =  null;
		
		if ( !e.getNodeName().equals(Server.SESSION_INIT) ) {
			throw new RDDLXMLException("not session init");
		}
		ArrayList<String> r = Server.getTextValue(e, Server.SESSION_ID);
		if ( r != null ) {
			c.id = Integer.valueOf(r.get(0));
		}
		r = Server.getTextValue(e, Server.NUM_ROUNDS);
		if ( r != null ) {
			c.numRounds = Integer.valueOf(r.get(0));
		}
		r = Server.getTextValue(e, Server.TIME_ALLOWED);
		if ( r!= null ) {
			c.timeAllowed = Double.valueOf(r.get(0));
		}
		r = Server.getTextValue(e, Server.TASK_DESC);
		if ( r!= null ) {
			rddlDesc = Base64.decode(r.get(0));
		}
		
		Records rec = new Records();
		
		rec.fileAppend("tmp.rddl", new String(rddlDesc), true);
		
		//read the file
		MyPath myPath = new MyPath();
		String absPath = System.getProperty("user.home") + System.getProperties().getProperty("file.separator") + "tmp.rddl";
		try {
			rddl = new RDDL(absPath);
		} catch (Exception e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		return c;
	}
	
	static String createXMLAction(ArrayList<PVAR_INST_DEF> ds) {
	//static String createXMLAction(State state, Policy policy) {
		try {  
			DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
			DocumentBuilder db = dbf.newDocumentBuilder();
			Document dom = db.newDocument();
			Element actions = dom.createElement(Server.ACTIONS);
			dom.appendChild(actions);
			for ( PVAR_INST_DEF d : ds ) {
				Element action = dom.createElement(Server.ACTION);
				actions.appendChild(action);
				Element name = dom.createElement(Server.ACTION_NAME);
				action.appendChild(name);
				Text textName = dom.createTextNode(d._sPredName.toString());
				name.appendChild(textName);
				for( LCONST lc : d._alTerms ) {
					Element arg = dom.createElement(Server.ACTION_ARG);
					Text textArg = dom.createTextNode(lc.toSuppString()); // TODO $ <>... done$
					arg.appendChild(textArg);
					action.appendChild(arg);
				}
				Element value = dom.createElement(Server.ACTION_VALUE);
				Text textValue = d._oValue instanceof LCONST 
						? dom.createTextNode( ((LCONST)d._oValue).toSuppString())
						: dom.createTextNode( d._oValue.toString() ); // TODO $ <>... done$
				value.appendChild(textValue);
				action.appendChild(value);
			}
			// Sungwook: a noop is just an all-default action, not a special
			// action.  -Scott
			//if ( ds.size() == 0) {
			//	Element noop = dom.createElement(Server.NOOP);
			//	actions.appendChild(noop);
			//}

			if (SHOW_XML) {
				Server.printXMLNode(dom);
				System.out.println();
				System.out.flush();
			}

			return serialize(dom);
		} catch (ParserConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}
	
	static int getANumber (DOMParser p, InputSource isrc, 
			String parentName, String name) {
		Element e = p.getDocument().getDocumentElement();
		if ( e.getNodeName().equals(parentName) ) {
			String turnnum = Server.getTextValue(e, name).get(0);
			return Integer.valueOf(turnnum);
		}
		return -1;
	}

	static long processXMLRoundInit(DOMParser p, InputSource isrc,
			int curRound) throws RDDLXMLException {
		try {
			p.parse(isrc);
		} catch (SAXException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
			throw new RDDLXMLException("sax exception");
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
			throw new RDDLXMLException("io exception");
		}
		Element e = p.getDocument().getDocumentElement();
		if ( !e.getNodeName().equals(Server.ROUND_INIT)) {
			return -1;
		}
		ArrayList<String> r = Server.getTextValue(e, Server.ROUND_NUM);
		if ( r == null || curRound != Integer.valueOf(r.get(0))) {
			return -1;
		}
		r =	Server.getTextValue(e, Server.TIME_LEFT);
		if ( r == null ) {
			return -1;
		}
		r = Server.getTextValue(e, Server.ROUND_LEFT);
		if ( r == null) {
			return -1;
		}
		
		return 0;
	}
	
	static long getTimeLeft(Element e) {
		ArrayList<String> r = Server.getTextValue(e, Server.TIME_LEFT);
		if ( r == null ) {
			return -1;
		}
		return Long.valueOf(r.get(0));
	}
	
	static ArrayList<PVAR_INST_DEF> processXMLTurn (Element e,
			State state) throws RDDLXMLException {

		if ( e.getNodeName().equals(Server.TURN) ) {
			
			timeAllowed = Double.valueOf(Server.getTextValue(e, Server.TIME_LEFT).get(0));
			
			// We need to be able to distinguish no observations from
			// all default observations.  -Scott
			if (e.getElementsByTagName(Server.NULL_OBSERVATIONS).getLength() > 0) {
				return null;
			}
			
			// FYI: I think nl is never null.  -Scott
			NodeList nl = e.getElementsByTagName(Server.OBSERVED_FLUENT);
			if(nl != null && nl.getLength() > 0) {
				ArrayList<PVAR_INST_DEF> ds = new ArrayList<PVAR_INST_DEF>();
				for(int i = 0 ; i < nl.getLength();i++) {
					Element el = (Element)nl.item(i);
					String name = Server.getTextValue(el, Server.FLUENT_NAME).get(0);
					ArrayList<String> args = Server.getTextValue(el, Server.FLUENT_ARG);
					ArrayList<LCONST> lcArgs = new ArrayList<LCONST>();
					for( String arg : args ) {
						if (arg.startsWith("@"))
							lcArgs.add(new RDDL.ENUM_VAL(arg));
						else // TODO $ <> (forgiving)... done$
							lcArgs.add(new RDDL.OBJECT_VAL(arg));
					}
					String value = Server.getTextValue(el, Server.FLUENT_VALUE).get(0);
					Object r = Server.getValue(name, value, state); // TODO $ <> (forgiving)... done$
					PVAR_INST_DEF d = new PVAR_INST_DEF(name, r, lcArgs);
					ds.add(d);
				}
				return ds;
			} else
				return new ArrayList<PVAR_INST_DEF>();
		}
		throw new RDDLXMLException("Client.processXMLTurn: Should not reach this point");
		//return null;
	}
	
	static double processXMLRoundEnd(Element e) throws RDDLXMLException {
		if ( e.getNodeName().equals(Server.ROUND_END) ) {
			ArrayList<String> text = Server.getTextValue(e, Server.ROUND_REWARD);
			if ( text == null ) {
				return -1;
			}
			return Double.valueOf(text.get(0));
		}
		return -1;
	}
			
	static double processXMLSessionEnd(DOMParser p, InputSource isrc) throws RDDLXMLException {
		try {
			p.parse(isrc);
		} catch (SAXException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
			throw new RDDLXMLException("sax exception");
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
			throw new RDDLXMLException("io exception");
		}
		Element e = p.getDocument().getDocumentElement();
		if ( e.getNodeName().equals(Server.SESSION_END) ) {
			ArrayList<String> text = Server.getTextValue(e, Server.TOTAL_REWARD);
			if ( text == null ) {
				return -1;
			}
			return Double.valueOf(text.get(0));
		}
		return -1;
	}
}

