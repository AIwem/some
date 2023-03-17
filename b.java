/*******************************************************************************
 * Copyright (c) 2009, 2011 The University of Memphis.  All rights reserved. 
 * This program and the accompanying materials are made available 
 * under the terms of the LIDA Software Framework Non-Commercial License v1.0 
 * which accompanies this distribution, and is available at
 * http://ccrg.cs.memphis.edu/assets/papers/2010/LIDA-framework-non-commercial-v1.0.pdf
 *******************************************************************************/
package edu.memphis.ccrg.lida.pam;

import edu.memphis.ccrg.alife.elements.ALifeObject;
import edu.memphis.ccrg.alife.elements.Cell;
import edu.memphis.ccrg.alife.elements.ObjectContainer;
import edu.memphis.ccrg.alife.world.ALifeWorld;
import edu.memphis.ccrg.lida.actionselection.ActionImpl;
import edu.memphis.ccrg.lida.actionselection.PreafferenceListener;
import edu.memphis.ccrg.lida.data.NeoUtil;
import edu.memphis.ccrg.lida.environment.Environment;
import edu.memphis.ccrg.lida.framework.FrameworkModule;
import edu.memphis.ccrg.lida.framework.FrameworkModuleImpl;
import edu.memphis.ccrg.lida.framework.ModuleListener;
import edu.memphis.ccrg.lida.framework.ModuleName;
import edu.memphis.ccrg.lida.framework.initialization.AgentStarter;
import edu.memphis.ccrg.lida.framework.initialization.Initializable;
import edu.memphis.ccrg.lida.framework.shared.*;
import edu.memphis.ccrg.lida.framework.shared.Node;
import edu.memphis.ccrg.lida.framework.tasks.FrameworkTaskImpl;
import edu.memphis.ccrg.lida.framework.tasks.TaskManager;
import edu.memphis.ccrg.lida.globalworkspace.BroadcastListener;
import edu.memphis.ccrg.lida.globalworkspace.Coalition;
import edu.memphis.ccrg.lida.globalworkspace.GlobalWorkspace;
import edu.memphis.ccrg.lida.language.GrammarTask;
import edu.memphis.ccrg.lida.pam.tasks.*;
import edu.memphis.ccrg.lida.workspace.Workspace;
import edu.memphis.ccrg.lida.workspace.WorkspaceContent;
import edu.memphis.ccrg.lida.workspace.WorkspaceListener;
import edu.memphis.ccrg.lida.workspace.workspacebuffers.WorkspaceBuffer;
//import org.jetbrains.annotations.NotNull;
//import org.jetbrains.annotations.Nullable;
import org.jetbrains.annotations.NotNull;
import org.neo4j.graphdb.*;
import org.opennars.control.GeneralInferenceControl;
import org.opennars.main.Nar;

import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.logging.Level;
import java.util.logging.Logger;

import static com.warmer.kgmaker.KgmakerApplication.graphDb;

/**
 * Default implementation of {@link PAMemory}. Module
 * essentially concerned with PamNode and PamLinks, source of meaning in LIDA,
 * how they are activated and how they pass activation among themselves.
 *
 * 知觉联想记忆默认实现。模块*本质上与PamNode和PamLinks有关，这是LIDA中的意义来源
 * 它们如何被激活以及它们之间如何传递激活
 * @author Ryan J. McCall
 */
public class PAMemoryImpl extends FrameworkModuleImpl
		implements PAMemory, BroadcastListener,
		WorkspaceListener, PreafferenceListener {

	private static final Logger logger = Logger
			.getLogger(PAMemoryImpl.class.getCanonicalName());
	private static ElementFactory factory = ElementFactory.getInstance();

	private static final String DEFAULT_NONDECAYING_PAMNODE = "NoDecayPamNode";

	private List<PamListener> pamListeners = new ArrayList<PamListener>();

	private Map termMap = new HashMap();


	/**
	 * A {@link NodeStructure} which contains all of the {@link PamNode},
	 * {@link PamLink} and their connections.
	 */
	protected PamNodeStructure pamNodeStructure = new PamNodeStructure(
			"PamNodeImpl", "PamLinkImpl");

	/**
	 * All {@link PamNode} objects currently in {@link PAMemoryImpl} indexed by their label.
	 */
	protected Map<String, PamNode> nodesByLabel = new ConcurrentHashMap<String, PamNode>();

	/**
	 * How PAM calculates the amount of activation to propagate PAM如何计算要传播的激活量
	 */
	private PropagationStrategy propagationStrategy = new UpscalePropagationStrategy();

	private static final int DEFAULT_EXCITATION_TASK_TICKS = 1;
	private int excitationTaskTicksPerRun = DEFAULT_EXCITATION_TASK_TICKS;

	private static final int DEFAULT_PROPAGATION_TASK_TICKS = 1;
	private int propagationTaskTicksPerRun = DEFAULT_PROPAGATION_TASK_TICKS;

	private static final double DEFAULT_PERCEPT_THRESHOLD = 0.7;	// 感知阈值
	private static double perceptThreshold = DEFAULT_PERCEPT_THRESHOLD;

	private static final double DEFAULT_UPSCALE_FACTOR = 0.6;

	protected double upscaleFactor = DEFAULT_UPSCALE_FACTOR;

	private static final double DEFAULT_DOWNSCALE_FACTOR = 0.5;
	private double downscaleFactor = DEFAULT_DOWNSCALE_FACTOR;
	
	private static final double DEFAULT_PROPAGATION_THRESHOLD = 0.05;	// 传播激活阈值
	private double propagateActivationThreshold = DEFAULT_PROPAGATION_THRESHOLD;

	private Map<Integer, LinkCategory> linkCategories = new HashMap<Integer, LinkCategory>();

	/**
	 * A map where an entry represents a mapping between one factory element type and another.
	 * The mapping governs a conversion that occurs for each Linkable send out of PAM as a percept.
	 * The most basic example would be: "PamNodeImpl","NodeImpl"
     *
     * 一种映射，其中的条目表示一种工厂元素类型与另一种工厂元素类型之间的映射。
     * 映射控制着从PAM发出的每个Linkable发送中发生的一次转换。
     * 最基本的示例是：“ PamNodeImpl”，“ NodeImpl”
	 */
	private Map<String,String> typeConversionMap = new HashMap<String,String>();

	/**
	 * Default constructor.
	 */
	public PAMemoryImpl() {
		super();
//		addInternalLinkCategory(DEFAULT_LINK_CATEGORY);
//		addInternalLinkCategory(LATERAL_LINK_CATEGORY); //TODO add back in for a release
//		addInternalLinkCategory(PARENT_LINK_CATEGORY);
//		addInternalLinkCategory(FEATURE_LINK_CATEGORY);
	}

	/**
	 * Will set parameters with the following names:
	 * pam.upscale the scaling on the amount of activation passed upwards
	 * from Nodes of lower conceptual depth to those of higher depth
	 * pam.downscale the scaling on the amount of activation passed
	 * downwards from Nodes of higher conceptual depth to those of lower depth
	 * pam.perceptThreshold the amount of activation a Node or Link must
	 * have to be part of the percept (be sent to the Workspace)
	 * pam.excitationTicksPerRun the delay (in ticks) on the excitation
	 * of Nodes and Links after they receive some activation, default is 1 tick
	 * pam.propagationTicksPerRun the delay (in ticks) on the propagation
	 * of activation from a Node or Link, default is 1 tick
	 * pam.propagateActivationThreshold the amount of activation
	 * necessary to be propagated i.e. a lesser amount is not (worth being) passed.
	 * pam.perceptMapping.* (String)- Can accept multiple mapping definitions of the form:
	 * mappingType:originalFactoryName:mappedFactoryname
	 * 
	 * 将使用以下名称设置参数：
	 * pam.upscale 从概念深度较低的节点向上传递到较高深度的节点的激活量的缩放
	 * pam.downscale从较高概念深度的节点向下传递到较低深度的节点的激活量的缩放
	 * pam.perceptThreshold节点或链接必须成为一部分的激活量的感知（发送到工作区） 
	 * pam.excitationTicksPerRun 节点和链接在收到一些激活后激发的延迟（以滴答为单位），默认为 1 个滴答
	 * pam.propagationTicksPerRun 从节点或链接传播激活的延迟（以滴答为单位），默认为 1 个滴答
	 * pam.propagateActivationThreshold 传播所需的激活量，即较小的数量不（值得）通过。
	 * pam.perceptMapping.（字符串）- 可以接受以下形式的多个映射定义：mappingType:origi nalFactoryName:映射的工厂名称
	 * 
	 * @see Initializable
	 */
	@Override
	public void init() {
		upscaleFactor=getParam("pam.upscale", DEFAULT_UPSCALE_FACTOR);
		downscaleFactor=getParam("pam.downscale",DEFAULT_DOWNSCALE_FACTOR);
		perceptThreshold=getParam("pam.perceptThreshold",DEFAULT_PERCEPT_THRESHOLD);
		excitationTaskTicksPerRun=getParam("pam.excitationTicksPerRun",DEFAULT_EXCITATION_TASK_TICKS);
		propagationTaskTicksPerRun=getParam("pam.propagationTicksPerRun",DEFAULT_PROPAGATION_TASK_TICKS);
		propagateActivationThreshold=getParam("pam.propagateActivationThreshold",DEFAULT_PROPAGATION_THRESHOLD);
		initTypeConversion();
//		pam = (PAMemoryImpl) AgentStarter.pam;
	}

	private void initTypeConversion() {
		Map<String,?> parameters = getParameters();
		for(String key: parameters.keySet()){
			if(key.startsWith("pam.perceptMapping.")){
				Object o = parameters.get(key);
				if(o instanceof String){
					String value = (String) o;
					String[] mappingParams = value.trim().split(",");
					if(mappingParams.length==3){
						if("node".equalsIgnoreCase(mappingParams[0])){
							if(factory.containsNodeType(mappingParams[1])&&
							   factory.containsNodeType(mappingParams[2])){
								typeConversionMap.put(mappingParams[1],mappingParams[2]);
							}else{
								logger.log(Level.WARNING,"One of the requested node types is not in the ElementFactory: {1}, {2}.",
										new Object[]{TaskManager.getCurrentTick(),mappingParams[1],mappingParams[2]});
							}
						}else if("link".equalsIgnoreCase(mappingParams[0])){
							if(factory.containsLinkType(mappingParams[1])&&
							   factory.containsLinkType(mappingParams[2])){
								typeConversionMap.put(mappingParams[1],mappingParams[2]);
							}else{
								logger.log(Level.WARNING,"One of the requested link types is not in the ElementFactory: {1}, {2}.",
										new Object[]{TaskManager.getCurrentTick(),mappingParams[1],mappingParams[2]});
							}
						}else{
							logger.log(Level.WARNING,"Bad mapping type: {1}. Must be 'node' or 'link'.",
										new Object[]{TaskManager.getCurrentTick(),mappingParams[0]});
						}
					}else{
						logger.log(Level.WARNING,"Mapping parameters must have 3 parts: " +
								"mappingType:originalType:mappedType separated by ','.",TaskManager.getCurrentTick());
					}
				}else{
					logger.log(Level.WARNING,"Mapping parameters must be of type String.",TaskManager.getCurrentTick());
				}
			}
		}
	}

	@Override
	public Environment getEnvironment() {
		return environment;
	}

	// todo 硬场景地点，要更智能
	public Environment environment;

	public GlobalWorkspace globalWorkspace;

	public WorkspaceBuffer csm;
	public WorkspaceBuffer nonGraph;
	public WorkspaceBuffer feelGraph;
	public WorkspaceBuffer goalGraph;
	public WorkspaceBuffer seqGraph;
	public WorkspaceBuffer concentGraph;
	public WorkspaceBuffer sceneGraph;
	public WorkspaceBuffer grammarGraph;

	public WorkspaceBuffer understandGraph;

	public NodeStructure csmNs;
	public NodeStructure nonNs;
	public NodeStructure feelNs;
	public NodeStructure conNs;
	public NodeStructure goalNs;
	public NodeStructure seqNs;
	public NodeStructure sceneNs;
	public NodeStructure yufaNs;

	public NodeStructure unNs;

//	public PAMemoryImpl pam;

	@Override
	public GlobalWorkspace getGlobalWorkspace() {
		return globalWorkspace;
	}

	@Override
	public WorkspaceBuffer getWorkspaceBuffer(String name) {
		switch (name){
			case "csm":
				return csm;
			case "goal":
				return goalGraph;
			case "non":
				return nonGraph;
			case "seq":
				return seqGraph;
			case "scene":
				return sceneGraph;
			case "con":
				return concentGraph;
			case "feel":
				return feelGraph;
			case "yufa":
				return grammarGraph;
			case "understand":
				return understandGraph;
			default:
				return nonGraph;
		}
	}

	// todo 注意力buffer，容易分类、增删查改、全局

	@Override
	public void setAssociatedModule(FrameworkModule m, String usage) {
		if (m instanceof Environment){
			environment = (Environment) m;
		}else if(m instanceof GlobalWorkspace){
			globalWorkspace = (GlobalWorkspace) m;
		}else if(m instanceof Workspace){
			csm = (WorkspaceBuffer) m.getSubmodule(ModuleName.CurrentSM);
			nonGraph = (WorkspaceBuffer) m.getSubmodule(ModuleName.NonGraph);

			feelGraph = (WorkspaceBuffer) m.getSubmodule(ModuleName.FeelGraph);
			goalGraph = (WorkspaceBuffer) m.getSubmodule(ModuleName.GoalGraph);
			seqGraph = (WorkspaceBuffer) m.getSubmodule(ModuleName.SeqGraph);

			concentGraph = (WorkspaceBuffer) m.getSubmodule(ModuleName.ConcentGraph);
			sceneGraph = (WorkspaceBuffer) m.getSubmodule(ModuleName.SceneGraph);
			grammarGraph = (WorkspaceBuffer) m.getSubmodule(ModuleName.GrammarGraph);

			understandGraph = (WorkspaceBuffer) m.getSubmodule(ModuleName.UnderstandGraph);

			csmNs = csm.getBufferContent(null);
			nonNs = nonGraph.getBufferContent(null);

			feelNs = feelGraph.getBufferContent(null);
			goalNs = goalGraph.getBufferContent(null);
			seqNs = seqGraph.getBufferContent(null);

			conNs = concentGraph.getBufferContent(null);
			sceneNs = sceneGraph.getBufferContent(null);
			yufaNs = grammarGraph.getBufferContent(null);

//			unNs = understandGraph.getBufferContent(null);
		}else{
			logger.log(Level.WARNING, "Cannot add module {1}",
					new Object[]{TaskManager.getCurrentTick(),m});
		}
	}

	@Override
	public void setPropagationStrategy(PropagationStrategy b) {
		propagationStrategy = b;
	}

	@Override
	public PropagationStrategy getPropagationStrategy() {
		return propagationStrategy;
	}

	/**
	 * @return the excitationTaskTicksPerRun
	 */
	public int getExcitationTaskTicksPerRun() {
		return excitationTaskTicksPerRun;
	}

	/**
	 * @return the propagationTaskTicksPerRun
	 */
	public int getPropagationTaskTicksPerRun() {
		return propagationTaskTicksPerRun;
	}

	@Deprecated
	@Override
	public Set<PamNode> addDefaultNodes(Set<? extends Node> nodes) {
		if (nodes == null) {
			return null;
		}
		Set<PamNode> storedNodes = new HashSet<PamNode>();
		for (Node n : nodes) {
			storedNodes.add(addDefaultNode(n));
		}
		return storedNodes;
	}

	@Override
	public PamNode addDefaultNode(Node n) {
		if (n == null) {
			return null;
		}
//		PamNode node = (PamNode) pamNodeStructure.addDefaultNode(n);
		PamNode node = (PamNode) pamNodeStructure.addNode(n,"PamNodeImpl");
		if (node.getName() != null) {
			nodesByLabel.put(node.getName(), node);
		}
		return node;
	}

	@Deprecated
	@Override
	public Set<PamLink> addDefaultLinks(Set<? extends Link> links) {
		if (links == null) {
			return null;
		}
		Set<PamLink> copiedLinks = new HashSet<PamLink>();
		for (Link l : links) {
			copiedLinks.add(addDefaultLink(l));
		}
		return copiedLinks;
	}

	@Override
	public PamLink addDefaultLink(Link link) {
		if (link == null) {
			return null;
		}
		// pam.addDefaultLink(l); 可以直接将未加入的node加入
		PamLink newlink = (PamLink) pamNodeStructure.addDefaultLink(link);
		return newlink;
	}
	
	@Override
	public PamNode addDefaultNode(String label){
		return addNode(pamNodeStructure.getDefaultNodeType(), label);
	}
	
	@Override
	public PamNode addNode(String type, String label){
		if(label == null){
			logger.log(Level.WARNING, "Cannot add a Node to Pam with a null label", 
					TaskManager.getCurrentTick());
			return null;
		}
		
		PamNode n = nodesByLabel.get(label);
		if(n != null){
			logger.log(Level.WARNING, "A Node with the label {1} already exists in PAM", 
					new Object[]{TaskManager.getCurrentTick(),label});
		}else{		
			n = (PamNode) pamNodeStructure.addNode(type,label,0.0,0.0);
			if(n != null){
				nodesByLabel.put(n.getName(), n);
			}
		}
		return n;
	}
	
	@Override
	public PamLink addDefaultLink(Node src, Linkable snk, LinkCategory cat){
//		return addLink(pamNodeStructure.getDefaultLinkType(), src, snk, cat);
		return (PamLink) pamNodeStructure.addDefaultLink(src,snk,cat,1.0,0.0);
	}
	
	@Override
	public PamLink addLink(String type, Node src, Linkable snk, LinkCategory cat){
		if(cat == null){
			logger.log(Level.WARNING, "Cannot add new Link. Category is null",
					TaskManager.getCurrentTick());
			return null;
		}

		return (PamLink) pamNodeStructure
				.addLink(type, src, snk, cat, 0.0, 0.0);
	}

	@Override
	public void addDetectionAlgorithm(DetectionAlgorithm detector) {
		PamLinkable pl = detector.getPamLinkable();
		if(pl == null){
			logger.log(
					Level.WARNING,
					"Detection algorithm {1} does not have a pamlinkable.",
					new Object[] { TaskManager.getCurrentTick(),detector});
			return;
		}
		if ( !pamNodeStructure.containsLinkable(pl)) {
			logger.log(Level.WARNING,
							"Adding detection algorithm {1} but, detector's pam linkable {2} is not in PAM.",
							new Object[] { TaskManager.getCurrentTick(),
									detector, detector.getPamLinkable() });
		}

		taskSpawner.addTask(detector);
		logger.log(Level.FINE, "Added feature detector to PAM", TaskManager
				.getCurrentTick());
	}

	@Override
	public void addPamListener(PamListener pl) {
		pamListeners.add(pl);
	}

	@Override
	public synchronized void receiveBroadcast(Coalition coalition) {
		learn(coalition);
	}

	Nar nar = AgentStarter.nar;

	@Override
	public void learn(@NotNull Coalition coalition) {
		csmNs.setBroadSceneCount(((NodeStructure) coalition.getContent()).getBroadSceneCount());

//		GeneralInferenceControl.selectConceptForInference(nar.memory, nar.narParameters, nar);

//		try (Transaction tx = graphDb.beginTx()) {
//			int ntruth;
//			boolean issinglenode = true;
//			for(Node node: csmNs.getNodes()){
//				ntruth = node.getTruth();
//				// 必须是单节点，不能是现成场景等结构，才能创建场景，后期场景亦可嵌套
//				for (Label lb: node.getNodeProxy().getLabels()) {
//					switch (lb.name()){
//						case"场景":
//							issinglenode = false;
//							break;
//						case"具身动作":
//							issinglenode = false;
//							break;
//						case"时序":
//							issinglenode = false;
//							break;
////						case"动词":break;
//						case"状态":
//							issinglenode = false;
//							break;
//						case"事件":
//							issinglenode = false;
//							break;
//					}
//				}
//				if (node.getLastAct().equals(String.valueOf(csmNs.getBroadSceneCount())) && issinglenode) {
//					// 当前新场景建模，理论上同时有几个为实点边，时序新建
//					if (ntruth == 1 || ntruth == 3 || ntruth == 5) {
//						for (int i = 0; i < 3; i++) {
////							System.out.println("新建节点id ----- " + graphDb.createNodeId());
//
//						}
//
//					}
//				}
//			}
//			tx.commit();
//		}

	}

	@Override
	public void decayModule(long ticks) {
		pamNodeStructure.decayNodeStructure(ticks);
	}

//	public static int k = 0;
	@Override
	public void excite(String object, double amount, String from) {
		Linkable linkable = getNode(object);

		if (linkable == null) {
			// 模态+场景+意象=三节点都要出现在无意识buffer
			// 如果只是取场景，又难联想到相关，太唯一+太确定，联想相关又可能爆炸
			linkable = pamNodeStructure.getNeoNode(object);

			// 查各感知节点
			// 感知节点，方案1：模态做场景标签，一个光秃秃的起点，查还需要标签，联动曲折
			// 方案2：模态与场景边链接，有外联动，模态本身可自行关联其他
			// pam查询大都通过点边联动，而非标签
//			linkable = NeoUtil.getNodeFrom(object,from);

			if (linkable != null) {
				// 首次执行
				// 上面linkable和节点本身激活为0，这里激活也为0
				addDefaultNode((Node) linkable);	// todo 性能、逻辑优化
			}
		}
		receiveExcitation(linkable, amount, from);
	}

	@Override	// 兴奋与激活不同，兴奋来自探测到的信息，激活是后续
	public void receiveExcitation(Linkable pl, double amount, String from) {
		if (pl instanceof PamLink) {
			logger.log(Level.WARNING, "Does not support pam links yet",
					TaskManager.getCurrentTick());
			return;
		}

//		ObjectContainer container = getObjectContainer();
//		String site = container.toString();
		// todo 这里相当于丘脑，汇集前端感知信息，包括纯符号。
		//  多线程如何整合？并不是整合=只是普通关联？也不能整合？会交互不等于整合？
		// todo 不用每次都查数据库，用缓存，暂时记忆
		// todo 性能、逻辑优化
		// pam不应该有整个图数据，而是要到图谱里取，pam取也是全局nodes取
		PamNode linkable = (PamNode) pamNodeStructure.getNode(pl.getExtendedId());

		if (linkable != null) {

			if(logger.isLoggable(Level.FINEST)){
				logger.log(Level.FINEST, "{1} receives excitation of: {2}",
						new Object[] { TaskManager.getCurrentTick(), linkable,
								amount });
			}
			addSite(linkable);

			double ww = 1.0;
//			try (Transaction tx = graphDb.beginTx()) {
//				try (Result result0 = tx.execute("match (n:死) return n", NeoUtil.parameters)) {
//					ww = (double) linkable.getNodeProxy(tx,"weight").getProperty("weight");
//				}
//				tx.commit();
//			}

			ww = (double) linkable.getProperty("weight");

			linkable.setActivation(ww*amount);

			// todo 分发信息=需要区别各模态，目前仅纯符号。各模态有快速通道，都与概念密切交互
			// todo 某信息激活度特高或对比度很强，自动调动自下而上注意力，与快速通道区别=概念无关
			// 这里修改linkable里的激活值，节点本身激活值为0，amount就是激活值
			ExcitationTask task = new ExcitationTask(excitationTaskTicksPerRun,
					linkable, amount, this);
			taskSpawner.addTask(task);
		} else {
			logger.log(Level.WARNING, "Cannot find pamnode: {1}", new Object[] {
					TaskManager.getCurrentTick(), pl });
		}
	}

	private void addSite(PamNode linkable) {
		ALifeWorld world = (ALifeWorld) getEnvironment().getModuleContent();
		ALifeObject agent = world.getObject("agent");
		Object o = agent.getAttribute("direction");

		char direction = (Character)o;
		Cell cell = (Cell) agent.getContainer();
		int x = cell.getXCoordinate();
		int y = cell.getYCoordinate();
        int x0 = x; // 中介
        int y0 = y;
		switch (direction){
			case 'N': y--;break;
			case 'S': y++;break;
			case 'E': x++;break;
			case 'W': x--;break;
		}
		String name = linkable.getName();

        if(name.equals("rockFront")){
            if (x>=0 && x < world.getWidth() && y>=0 && y<world.getHeight()) {
                // 貌似只有石头需要预测位置，其他都是智能体当前位置即可，
                // 石头不可以进入，石头在哪就标记在哪
                linkable.setLocation(x + "_" + y);
            }else {
            	// 石头超界？
				linkable.setLocation(x0 + "_" + y0);
				System.out.println("rockFront？？？？？---------------------------------------");
			}
        }else {
        	// 空和出界都可以存当前位置，表示当前位置遇到了
			// 空本身可以进入，当前位置空则保存空，当前空和下个格空都可
			linkable.setLocation(x0 + "_" + y0);
		}
	}

//	Queue tasks = KgmakerApplication.nar.memory.newTasks;

	public static LinkedList tasklist = new LinkedList();

	@Override
	public void receiveExcitation( Set<PamLinkable> linkables, double amount, String from) {
		for (PamLinkable linkable : linkables) {
			receiveExcitation(linkable, amount, from);
		}
	}

	private Map<String, Object> propagateParams = new HashMap<String, Object>();

	@Override	// todo 与nars入口整合，整合memory和ns，点边和concept
	public void propagateActivationToParents( Node pn, int deep, String from) {
		double currentActivation = pn.getActivation();
		String pname = pn.getName();
		String sname = "";
		Node sink;

		putMap(pn, pname);

//		if (from.equals("varscene") || from.equals("varisa")) {
//			pn.setActivation(pn.getActivation() + 0.3);
////			System.out.println(pn.getName() + "-----------激活后来是------" + pn.getActivation());
//		}

		String bcastid = String.valueOf(csmNs.getBroadSceneCount() + 1);
		// 以下几个参数，只要激活到这里，无论是否激活下去，都更新
		// 设置周期，在广播时统一
		pn.setBcastid(bcastid);
		// 最后激活周期，非留存衰减的
		pn.setLastAct(bcastid);

		int currentstate = 0;
		int exsittruth;
		// 上周期虚实以通达为准，其次为无意识
//		Node nonexistnode = nonNs.getNode(pn.getNodeId());
		Node csmexistnode = csmNs.getNode(pn.getNodeId());

		// 非联想到的点，直接报告意识，符号不一定连续，且不一定同模态
		// 视网膜物理筛选+丘脑程序筛选+情感有意筛选，即使专注思考，现实感知也不会“闪断”
		// 从感知来（0）则直接用from，否则都是联想思考，根据实际改from，无场景点边都是默认想象
		// 十三个from，感知六感，想象七感，包括默认，具身感觉可以直接转为体验？
		// 过阈值通达的肯定是涉及意象，和过阈值的无意象一起受丘脑调控，不过阈值的意象不用调控
		// 联想模态从点和场景来，没体验的想象需要判断，猫叫既可能是视觉，也可能是听觉
		if (deep != 0) {
//			from = "想象";

			if (csmexistnode != null) {
				exsittruth = csmexistnode.getTruth();
				// 不存在已有节点，场景不可能直接从实开始
				if (AgentStarter.actmap.containsKey(pname)) {
					// 目前虚，有已存在节点
					currentstate = getCurrentstate(pname, exsittruth, true, false);
				} else if (AgentStarter.statemap.containsKey(pname)) {
					currentstate = getCurrentstate(pname, exsittruth, true, true);
				} else {
					// 目前虚，有已存在节点
					currentstate = getCurrentstate(currentstate, exsittruth);
				}

			} else {
				// 具身动作等，如果场景只有一个核心，没有已存在节点，也可能为实，看核心虚实
				if (AgentStarter.actmap.containsKey(pname)) {
					currentstate = getCurrentstate(pname, 0, false, false);
				}
			}
			pn.setTruth(currentstate);
		} else {
			currentstate = 1;
			if (csmexistnode != null) {
				exsittruth = pn.getTruth();
				// 之前是+现在是=整合结果
				currentstate = getCurrentstate(currentstate, exsittruth);
			} else {
				currentstate = 1;
			}
			pn.setTruth(currentstate);

//			pn.setFromsceneid();

			// 激活开始，往后的激活都有sink把三元组头部加入了
			pamListeners.get(0).receivePercept(pn, ModuleName.NonGraph);
			// 感官输入，加入内容备选buffer
			pamListeners.get(0).receivePercept(pn, ModuleName.ConcentGraph);
		}
//		pamNodeStructure.addNode(pn,true);
		pamNodeStructure.addNode(pn, "PamNodeImpl");
//		pamNodeStructure.addDefaultNode(pn);

		boolean isover = false;
		// todo 思维控制+注意力，buffer调控，主链路+次分支
//		if (from.equals("varwantplan") && deep < 10) {
//			isover = true;
//		} else if ((from.equals("varscene") || from.equals("varisa")) && deep < 9) {
//			isover = true;
//		} else
		if (deep < 6) {	//启发扩散只允许6层，否则会导致深度过深，无限激活，其他交给约束搜素
			isover = true;
		}

		// todo 可能加上脉冲或抑制。被交叉激活频率也代表信息强度，一定程度
		// todo 可能不是随机激活，需要有方向、类型、深度等限制
		// todo 思考场景内容
//		if ((currentActivation >= propagateActivationThreshold && deep < 6)) {
		if (isover) {
			deep++;

			// todo 专门的情绪感觉模块，特定self子图，长链关联到当前场景，
			//  场景子图=注意+实例化+推理+情绪+动机，特定话语对特定场景对不对，
			//  反思还包括是否这特定场景，找上下文场景，甚至完全改变场景属性
			// Calculate the amount to propagate //计算传播量=传递值=权重*激活来源
			propagateParams.put("upscale", upscaleFactor);
			propagateParams.put("totalActivation", pn.getTotalActivation());
			double amountToPropagate = propagationStrategy.getActivationToPropagate(propagateParams);

			double pnact = pn.getActivation();
			boolean isExists = false;
			String fromlinktype = pn.getFromLinkType();

			Set<Link> parentLinkSet = new HashSet<>();
			// 多线程，列表修改，报错，加锁貌似也不行

			if (pname.equals("ft111") || sname.equals("ft111")) {
				System.out.println("---------ft111-----------sink---------------");
			}

			parentLinkSet = pamNodeStructure.getConnectedSinks(pn);

			// todo 查找出来的也添加到子图，这里相当于无意识子图，不广播，但包含感知信息
			// todo 区分意识和无意识部分，不是所有都要广播，加上动机+融入推荐交互
			//  不应期有两个？广播不应期+传递不应期，这里传递不应期=要对应单个神经冲动=具体看性质+语义性传递也可单位化
			// 激活衰退可近似不应期衰退，但有特殊衰退策略的不行
			for (Link parent : parentLinkSet) {
				sink = (Node) parent.getSink();
				sname = sink.getName();
				// 避免循环激活，todo 非循环环状激活避免
				if (pn.getFromnodeid() == sink.getNodeId()) {
					continue;
				}
//				Link checklink = nonNs.getLink(parent.getExtendedId());
//				if(checklink != null && checklink.getActivation() >= 0.95){
//					System.out.println("----单传递不应期----跳过---------------");
//					continue;
//				}

				Node checkSink = nonNs.getNode(sink.getExtendedId());
				if(checkSink != null && checkSink.getActivation() >= 0.98){
					System.out.println("----单传递不应期----跳过---------------" + sname);
					continue;
				}

				putMap(sink, sname);
				// 重设fromnodeid，避免循环激活
				parent.getSource().setFromnodeid(pn.getFromnodeid());

				// 睡前buffer，含临时点边，不衰减，只记忆移除
				pamNodeStructure.addNode(sink, "PamNodeImpl");
				pamNodeStructure.addLink(parent, "PamLinkImpl");

				Set<Link> linksofsink = new HashSet<>();
				String pcate = parent.getCategory().getName();

				// sink如果是概念，概念和非意象属性都不通达，内隐联想
				// 现实=当前，预测=scene，限制一度搜索，其他则是联想。场景需要完整才通达
				// 联想必须通过意象展现，而不是点边，信息转换生成与丘脑交互复杂
				// 概念等属性也需要转为意象，语言化,如听觉文本，“这个是XX”、“XX！！”
				// agi本身可不限制通达，但要避免认知错乱+无意义信息+处理不完+不灵活+性能低
				for (Link l : nonNs.getLinksOfSink(sname)) {
					linksofsink.add(l);
					if (l.getExtendedId().toString().equals(parent.getExtendedId().toString())) {
						isExists = true;
					}
				}

				int lofssize = linksofsink.size();

				SetAct(sink, lofssize, pcate);
				// 激励来自动机
				double linkincentive = 0.1;
				if (pcate.equals("欲求") || pcate.equals("顺承")) {
//						linkincentive = (Double) parent.getLinkProxy().getProperty("incentive");
					linkincentive = (Double) parent.getProperty("incentive");
				}
				double pnincentive = pn.getIncentiveSalience();

				boolean isisascence = false;
				boolean iswant = false;
				boolean isforwork = false;
				boolean iscontains = false;
				// 语言编码类似编译词法分析，识别关键字，区别对待，链接到对应位置，对应模块
				// 目前阶段是语言运行时，已编译好的语言，按部就班、分门别类，进行认知层运算
				switch (pcate) {
					case "欲求":
						sink.setIncentiveSalience(linkincentive);
						parent.getSink().setIncentiveSalience(linkincentive);
						pamListeners.get(0).receivePercept(pn, ModuleName.FeelGraph);
						// 内隐动机，感觉--欲求场景整体。加入buffer利于跨周期，与意识同理
						iswant = true;
						System.out.println("欲求-------------- " + sname + "-------------" + linkincentive);
						pamListeners.get(0).receivePercept(pn, ModuleName.GoalGraph);
						pamListeners.get(0).receivePercept(sink, ModuleName.GoalGraph);
						pamListeners.get(0).receivePercept(parent, ModuleName.GoalGraph);
						Set<Link> linkSet0 = NeoUtil.getSomeLinks(sink, null, null, null, null);
						for (Link link : linkSet0) {
							// 动作和内容都加入，以便判定跨越式计划对应动作，具体内容根据实际场景
							pamListeners.get(0).receivePercept(link.getSource(), ModuleName.GoalGraph);
							pamListeners.get(0).receivePercept(link, ModuleName.GoalGraph);
						}
						break;
					case "子类":
					case "心理计划":// 计划为头部，需要把pn加入，接下来的时序则不用头部
					case "具身计划":
//					case "时序首": // 时序的开头，也许能减少遍历，但构建麻烦，查找也麻烦，一般查“时序”
					case "时序":
//						if (seqNs.containsNode(pn)) {
						// 激励为0，则不在当前计划中，但可以进入备描述内容，抽象方法论描述
						if (pnincentive <= 0) {
							// 时序执行时描述 = 方法过程实例化，分开控制，实时赋值运算
							// 不执行也可参考以往经验，描述一些可能情况、细节和具体案例
//							if(seqNs.containsNode(pn)){
//								pamListeners.get(0).receivePercept(pn,ModuleName.ConcentGraph);
//								pamListeners.get(0).receivePercept(sink,ModuleName.ConcentGraph);
//								pamListeners.get(0).receivePercept(parent, ModuleName.ConcentGraph);
//							}
						} else {
							if (pcate.equals("时序")) {
								sink.setIncentiveSalience(pnincentive - 0.01);
							} else {
								sink.setIncentiveSalience(pnincentive);
							}

//							pamListeners.get(0).receivePercept(pn,ModuleName.SeqGraph);
							pamListeners.get(0).receivePercept(sink, ModuleName.SeqGraph);
							pamListeners.get(0).receivePercept(parent, ModuleName.SeqGraph);
//							}
						}
						break;
					case "顺承":
						isforwork = true;
						int pntruth = pn.getTruth();
						// 如果实现了中间状态，则下一计划节点激励累加，再激励加成
						// 双实，双虚，虚实，实虚，累积策略
						if (pntruth == 3 || pntruth == 5) {
							sink.setIncentiveSalience(sink.getIncentiveSalience() + pnincentive * linkincentive + 0.2);
						} else {
							sink.setIncentiveSalience(sink.getIncentiveSalience() + pnincentive * linkincentive);
						}
						// 计划里有无都算激励，非备选动作不经过动作选择，但可评估时序价值
						// 方法论buffer是否需要再论，还有其他各类型，认知层，非本能层
						if (seqNs.containsNode(pn) && seqNs.containsNode(sink)) {
							pamListeners.get(0).receivePercept(pn, ModuleName.SeqGraph);
							pamListeners.get(0).receivePercept(sink, ModuleName.SeqGraph);
							pamListeners.get(0).receivePercept(parent, ModuleName.SeqGraph);
						} else if (seqNs.containsNode(pn) || seqNs.containsNode(sink)) {
//							System.out.println("并非头尾都在计划buffer中----||||--" + parent.toString());
							// 无序激活，有些时序没来得及加入，则需要识别当前顺承链接是否进入
							getSucc(pn, sink, parent);
						}
						break;
					case "内容":
						break;
					case "isa":// 场景内变量实例化 todo 变量外属性化=语句化
						if (AgentStarter.scenemap.containsKey(pname) && AgentStarter.scenemap.containsKey(sname)) {
							if(taskSpawner.getTasks().size() > 1000){
								continue;
							}
							if (AgentStarter.varscenemap.containsKey(sname)) {
								isisascence = true;
								// 变量式激活延伸和蕴含网，都含isa，可以放在一起讨论？
								IsaPamTask isaPamTask = new IsaPamTask(pn,sink,this,pamNodeStructure,seqNs, "normal");
								taskSpawner.addTask(isaPamTask);
							}
						}
						// todo 会循环激活，目前只有蕴含链开头有isa？
						if (fromlinktype.equals("isa") || fromlinktype.equals("蕴含") || deep == 1) {
							// 按是否联通判断，并加入语义网，非语义网的会孤立
							pamListeners.get(0).receivePercept(pn, ModuleName.ConcentGraph);
							pamListeners.get(0).receivePercept(sink, ModuleName.ConcentGraph);
							pamListeners.get(0).receivePercept(parent, ModuleName.ConcentGraph);
							sink.setActivation(sink.getActivation() + 0.1);
							if(deep == 6){
								deep = 5; // 理解链可继续延伸，并还能扩散一度，像蜈蚣
							}
							retrieve(parent);
						}
						break;
					case "语序":
						// 当前处理的语法框架为main
//						yufaNs.setMainNodeId(sink.getNodeId());

//						if(!yufaNs.containsLink(parent)){
//							int ssize = yufaNs.getLinksOfSink(sink.getNodeId()).size();
//							sink.setDoneNum(ssize + 1);
//						}

//						if(sink.getNodeId() == yufaNs.getMainNodeId() || yufaNs.getMainNodeId() != 0){
//							break;
//						}
					case "顺接":
						pamListeners.get(0).receivePercept(pn, ModuleName.GrammarGraph);
						pamListeners.get(0).receivePercept(sink, ModuleName.GrammarGraph);
						pamListeners.get(0).receivePercept(parent, ModuleName.GrammarGraph);
						break;
					case "蕴含":
						if (fromlinktype.equals("isa") || fromlinktype.equals("蕴含") || deep == 1) {
							// 按是否联通判断，并加入语义网，非语义网的会孤立
							// 要属性齐全才能继续往下传，不能只有光杆蕴含链
							pamListeners.get(0).receivePercept(pn, ModuleName.ConcentGraph);
							pamListeners.get(0).receivePercept(sink, ModuleName.ConcentGraph);
							pamListeners.get(0).receivePercept(parent, ModuleName.ConcentGraph);
							sink.setActivation(sink.getActivation() + 0.1);
							if(deep == 6){
								deep = 5; // 理解链可继续延伸，并还能扩散，像蜈蚣。保留强扩散的影响能力=开小差
							}
							retrieve(parent);
						}
						break;
					case "返回赋值":
					case "整体赋值":
					case "赋值":
					case "满足":
					case "else":
						// 只要头节点在时序buffer，这几类边就肯定会进入buffer，顺承则不一定
						if (seqNs.containsNode(pn) && pnincentive > 0) {
							sink.setIncentiveSalience(pnincentive);
							pamListeners.get(0).receivePercept(pn, ModuleName.SeqGraph);
							pamListeners.get(0).receivePercept(sink, ModuleName.SeqGraph);
							pamListeners.get(0).receivePercept(parent, ModuleName.SeqGraph);
						}
						break;
					default:
						break;
				}
				// 语义网边类型较杂
//				if (conNs.containsNode(sink) || conNs.containsNode(pn)) {
				if (deep == 1) {
					pamListeners.get(0).receivePercept(sink, ModuleName.ConcentGraph);
					pamListeners.get(0).receivePercept(parent, ModuleName.ConcentGraph);
				}
				// 如果不是当前实例化，而sink是有变量场景，则判断是否已经实例化，有则激活
				// 当前实例化已经激活一遍，无需再激活，局限于单条isa链接，顺承、蕴含、动机放行
//				if (!isisascence && (iscontains || isforwork || iswant)) {
//					GoalTask goalTask = new GoalTask(sink,this,seqNs,nonNs,goalNs,iswant,"normal");
//					taskSpawner.addTask(goalTask);
//				}

				// 无论无意识有没有，超阈值都可以通达
//				if (sink.getActivation() > 0.5) {
				if (isOverPerceptThreshold(sink)) {
					boolean isin = false;
					// 两条边以上，且是场景，则入csm，三要素要判断
					if ((!isExists && lofssize > 0) || (isExists && lofssize > 2)) {
						isin = true;
						// 无意识没有sink，则没有link
						for (Link l : nonNs.getLinksOfSink(sname)) {
							if (csmNs.containsNode(l.getSource().getExtendedId())) {
								pamListeners.get(0).receivePercept(l, ModuleName.CurrentSM);
							}
						}
					} else if (isExists && lofssize == 1) {
						isin = true;
					}

					if (isin) {// 三个要齐全才显示完
						pamListeners.get(0).receivePercept(pn, ModuleName.CurrentSM);
						pamListeners.get(0).receivePercept(sink, ModuleName.CurrentSM);
						pamListeners.get(0).receivePercept(parent, ModuleName.CurrentSM);
					}
				}
				// 无论能不能过阈值，都加入睡前缓存+无意识buffer，激活值偏低
				pamListeners.get(0).receivePercept(sink, ModuleName.NonGraph);
				pamListeners.get(0).receivePercept(parent, ModuleName.NonGraph);

				if (pname.equals("事物")) {
					System.out.println("事物的fromid --------" + pn.getFromnodeid());
				}

				// 设置来源id，来源场景id为pn自带
				sink.setFromsceneid(pn.getFromsceneid());
				sink.setFromnodeid(pn.getNodeId());
				sink.setFromLinkType(parent.getCategory().getName());

				if (!pcate.equals("顺接")) {
					// 传递一层一条一个线程
					propagateActivation(sink, (PamLink) parent, amountToPropagate, deep, from);
				}
			}
		}
	}

	private void getSucc( Node pn, Node sink, Link parent) {
		String query = "match (n:场景)<-[r:时序]-(m:场景)-[r0:时序]->(i:场景) where n.name = \'" 
				+ pn.getName() + "\'  and i.name = \'" + sink.getName()  + "\' return m";
		Link link0;
		try (Transaction tx0 = graphDb.beginTx()) {
			try (Result result0 = tx0.execute(query, NeoUtil.parameters)) {
				Map<String, Object> row0;
				String scenename;
				while (result0.hasNext()) {
					System.out.println("query = " + query);
					row0 = result0.next();
					org.neo4j.graphdb.Node scene;
					for (String key0 : result0.columns()) {
						scene = (org.neo4j.graphdb.Node) row0.get(key0);
						scenename = (String) scene.getProperty("name");
						if(seqNs.containsNode(((Long)scene.getId()).intValue())){
							Node n = seqNs.getNeoNode(scenename);
							if(n.getIncentiveSalience() > 0){
								pn.setIncentiveSalience(n.getIncentiveSalience());
								sink.setIncentiveSalience(n.getIncentiveSalience());
								pamListeners.get(0).receivePercept(pn, ModuleName.SeqGraph);
								pamListeners.get(0).receivePercept(sink, ModuleName.SeqGraph);
								pamListeners.get(0).receivePercept(parent, ModuleName.SeqGraph);
							}
						}
					}
				}
			}
			tx0.commit();
		}
	}
	// todo 认知执行语句化，在类似nars时序上执行，尽量不用线程？语句只是小图程，直接替换并改元组即可，大图程还需线程
	// 		图程需要动机管理分配，不能直接根据时序连续执行，集中管理=能派生+能中断+能回溯
	@Override
	public void getActRoot( Link link) {
		Node sink = (Node) link.getSink();
		Node source = link.getSource();
		putMap(sink,sink.getName());
		// 从时序首开始执行，递归查找到最上头时序 
		String query = "match (m:场景)-[r:时序首]->(i:场景) where m.name = \'" + sink.getName() + "\' return r";
		System.out.println("query = " + query);
		Link link0 = null;
		try (Transaction tx0 = graphDb.beginTx()) {
			try (Result result0 = tx0.execute(query, NeoUtil.parameters)) {
				Map<String, Object> row0;
				while (result0.hasNext()) {
					row0 = result0.next();
					Relationship actre;
					for (String key0 : result0.columns()) {
						actre = (Relationship) row0.get(key0);

						link0 = NeoUtil.CastNeoToLidaLink(actre,null);
						Node toNode = (Node)link0.getSink();
						// 每个时序分别加入计划，以备执行，头节点已有，不用加入
						pamListeners.get(0).receivePercept(toNode,ModuleName.SeqGraph);
						pamListeners.get(0).receivePercept(link0, ModuleName.SeqGraph);

						toNode.setIncentiveSalience(sink.getIncentiveSalience());

						System.out.println("时序首---|||-" + link0.toString());

						// 即使当前层时序已经在这里找到并执行，还需要激活非时序节点，如满足和else？
						// 只需找到时序就行，时序节点具体是什么类型，再根据类型执行，往下就往下，如满足和else
//						propagateActivation(toNode, (PamLink) link0, 1.0, 1, "varmindplan");
					}
				}
			}
			tx0.commit();
		}

		if(link0 != null) {
			// 如果有可能的后续嵌套时序，则将上位时序存入主路线，以便回溯执行
			// 循环时序+判断时序，都会进入这里。时序执行逻辑一样，判断时序的上位是判断边，A--判断（首）--》B
			seqNs.getMainPath().add(link);
			// 尾递归查找执行全部子时序
			getActRoot(link0);
		}else {

			AgentStarter.isDoVar = true;
			AgentStarter.startick = TaskManager.getCurrentTick();

			// 这里是尽头，后面没有时序，从这根据节点类型开始执行具体逻辑
			// 跨过当前节点，可能还有时序，要先执行完当前阶段所有可执行节点，里面可能还要递归
			if(AgentStarter.varscenemap.containsKey(sink.getName())){

				DoMindActTask doMindActTask = new DoMindActTask(sink,source,this, seqNs, sceneNs);
				taskSpawner.addTask(doMindActTask);

			}else if(AgentStarter.ifelsemap.containsKey(sink.getName())){

                SelectTreeTask selectTreeTask = new SelectTreeTask(link, this, sceneNs);
                taskSpawner.addTask(selectTreeTask);

			}else {
				SimpleSceneTask simpleSceneTask = new SimpleSceneTask(sink,source,this,sceneNs);
				taskSpawner.addTask(simpleSceneTask);
			}

//			doSucc(link, sink, source);
//			DoSuccTask doSuccTask = new DoSuccTask(sink,source,this);
//			taskSpawner.addTask(doSuccTask);
		}
	}

	// 点边分类，模拟硬件立体，buffer阶段性分类，扩散后匹配框架，利于结构性推理
	@Override
	public void putMap( Node node, String name) {
		Long core;
		for (String lb: node.getLabels()){
			switch (lb){
				case "具身动作":
					// 场景核心数，1是具身动作不及物，2是及物具身动作，3是主谓宾
					core = (Long) node.getProperty("core");
					AgentStarter.actmap.put(name,core.intValue());
					break;
				case "心理动作":
//					core = (Long) node.getNodeProxy().getProperty("core");
//					AgentStarter.mindactmap.put(name,core.intValue());
					AgentStarter.mindactmap.put(name,1);
					break;
				case "场景":
					AgentStarter.scenemap.put(name,1);
					break;
				case "情感":
					AgentStarter.feelmap.put(name,1);
					break;
				case "时序":
					AgentStarter.seqmap.put(name,1);
					break;
				case "动作":
					AgentStarter.actmap.put(name,1);
					break;
				case "状态":
					core = (Long) node.getProperty("core");
					AgentStarter.statemap.put(name,core.intValue());
					break;
				case "变量":
					AgentStarter.varmap.put(name,1);
					break;
				case "语法":
					AgentStarter.yufamap.put(name,1);
					break;
				case "语法槽":
					AgentStarter.facaomap.put(name,1);
					break;
				case "ifelse":
					AgentStarter.ifelsemap.put(name,1);
					break;
				case "循环":
					AgentStarter.formap.put(name,1);
					break;
				case "变量场景":
					AgentStarter.varscenemap.put(name,1);
					break;
				default:break;
			}
		}
	}

	private void retrieve(Link parent) {
		String pcate = parent.getCategory().getName();
		switch (pcate){
			case "isa":
				break;
			case "蕴含":
				break;
			default:
				break;
		}
		// 反向推理，激活对标场景或语义框架，类比输入信息理解，判断是否符合对应
		// todo 独立线程？


		for (Node node: goalNs.getNodes()) {	// todo 动机生成立刻控制注意
			for (String lb : node.getLabels()) {
				// todo 实际上约束搜索是广泛且不限模块，纯理解+脑内语言+交流语言+视听想象
				if (lb.equals("语言生成")) {
					String nname = node.getName();
					String sourcename = parent.getSource().getName();
					int fromnodid = parent.getSource().getFromnodeid();
//					String query;
					// 如果是对象，下文非对象，则触发联合搜索
					if (sourcename.equals("事物")){
						// 默认找下文，上文被上一周期处理了
						for (Link l : nonNs.getLinksOfSource(fromnodid)){
							if (l.getName().equals("fto")){
								for (Link l0 : nonNs.getLinksOfSource(((Node)l.getSink()).getNodeId())){
									if (l0.getName().equals("isa")){
//										fatch(fromnodid, l0);
									}
								}
							}
						}
					}else {

					}
				}
			}
		}
	}

	private void fatch(int fromnodid,  Link l0) {
		String query = "match p = (n)<-[r:isa]-(m)-[r0:动作]->(i:场景)<-[r1]-(o) where n.name = \'" + 
				l0.getSink().getName() + "\'  and o.name = \'" + nonNs.getNode(fromnodid).getName() + "\' return i";
		System.out.println("query = " + query);
		try (Transaction tx0 = graphDb.beginTx()) {
			try (Result result0 = tx0.execute(query, NeoUtil.parameters)) {
				Map<String, Object> row0;
				while (result0.hasNext()) {
					row0 = result0.next();
					org.neo4j.graphdb.Node scene;
					String scenename;
					for (String key0 : result0.columns()) {
						scene = (org.neo4j.graphdb.Node) row0.get(key0);
						scenename = (String) scene.getProperty("name");

						System.out.println("约束搜索到场景 ----" + scene.getProperty("name"));

						// todo 不硬编码
						if (!scenename.equals("ft0")) {
                            sceneNs.setMainNodeId(((Long)scene.getId()).intValue());
							getSceneNode(NeoUtil.getPamNode(scene,scenename), scenename,false);
						}
					}
				}
			}
			tx0.commit();
		}
	}

	@Override
	public void setSceneMainNode(Node sink) {
		if (sceneNs.getMainNodeId() != 0){
			boolean isesxit = false;
			for (String sceneId: AgentStarter.scenelist){
				if (sceneId.equals(String.valueOf(sink.getNodeId()))){
					isesxit = true;
					break;
				}
			}
			// 如果没有待生成的场景，而还有mainid，则直接覆盖，遗留的无用mainid
			if(sceneNs.getNodes().size() == 0){
				sceneNs.setMainNodeId(sink.getNodeId());
				AgentStarter.scenelist.clear();
			}else if (!isesxit) {
				AgentStarter.scenelist.add(String.valueOf(sink.getNodeId()));
			}
		}else {
			sceneNs.setMainNodeId(sink.getNodeId());
		}
	}

	@Override
	public void getSceneNode(Node scene, String scenename, boolean isvar) {
		String query;
		// 进入场景buffer默认是语言生成或视听想象，普通场景直接通达
		query = "match (n{name:\'" + scenename + "\'})<-[r]-() return r";
		try (Transaction tx1 = graphDb.beginTx()) {
			try (Result result = tx1.execute(query, NeoUtil.parameters)) {
				int num = 0;
				while (result.hasNext()) {
					num++;
					getScene(result, isvar);
				}
				// 有语法被激活，且为主场景，则触发语法框架建模任务，尽量只一次
				if (num != 0 ) {
					if(scene.getNodeId() == sceneNs.getMainNodeId()){
						// 每个场景一个任务，包括子场景？
						GrammarTask task = new GrammarTask(yufaNs, sceneNs,1,this);
						taskSpawner.addTask(task);
					}
					for(String sceneId : AgentStarter.scenelist){
						if(sceneId.equals(String.valueOf(scene.getNodeId()))){
							// 如果接下来的时序执行也激活了，那同样激活语法任务
							GrammarTask task = new GrammarTask(yufaNs, sceneNs,1,this);
							taskSpawner.addTask(task);
						}
					}

				}
			}
			tx1.commit();
		}
	}

	private void getScene( Result result,boolean isvar) {
		Link link;
		Map<String, Object> row = result.next();
		Relationship re;
		String retype;
		Node fromNode = null;
		Node toNode = null;
		for ( String key : result.columns() ) {
			re = (Relationship) row.get(key);
			retype = re.getType().toString();
			if (retype.equals("顺承")) continue;
			if (retype.equals("时序")) continue;
			if (retype.equals("时序首")) continue;
			if (retype.equals("参数")) continue;

			link = NeoUtil.CastNeoToLidaLink(re,null);
			toNode = (Node)link.getSink();
			pamNodeStructure.addNode(toNode,"PamNodeImpl");
			if(isvar){
				Map<String,Object> resultmap = getIsaLink(link.getSource(), toNode, link.getCategory(),this);
				if (resultmap.get("done").equals("yes")){
					link = (Link) resultmap.get("link");
				}
			}

			fromNode = link.getSource();
			putMap(fromNode,fromNode.getName());

			putMap(toNode,toNode.getName());

			// 如果待生成的是场景，继续纳入场景元素以备生成，
			// 在场景buffer之后，父场景边语法激活之前？
			// 避免子场景先集齐语法框架输出，已在语法任务激活时控制
			if(AgentStarter.scenemap.containsKey(fromNode.getName())){
				getSceneNode(fromNode,fromNode.getName(),isvar);
			}

			activGrammarLink(link, retype);

		}
	}

	@Override
	public Map getIsaLink(Node node, Node toNode, LinkCategory category, PAMemory pam) {
		Link link;
		Map<String,Object> thisresult = new HashMap<>();
		// 初始化返回map，如果下面没有被更新，则没有新建边，因为没有nowisa
		thisresult.put("done","no");
		for (Link l :seqNs.getLinksOfSource(node.getNodeId())){
			if(l.getName().equals("nowisa")){
				thisresult = getIsaLink((Node) l.getSink(),toNode,category,pam);
				if (thisresult.get("done").equals("yes")){
					// 如果已经新建边，则直接层层返回；
					return thisresult;
				}
				// 上面没有直接返回，证明还没新建边，如果是含变量场景，则替换为现值
				link = pam.addDefaultLink((Node)l.getSink(), toNode, category);
				thisresult.put("link",link);
				thisresult.put("done","yes");
			}
		}
		return thisresult;
	}

	@Override
	public void activGrammarLink(Link link, String retype) {
		Linkable linkable;
		// 用于生成的场景，可用来对应语法结构，以场景为准，拼接语法框架=更灵活多变可变
		pamListeners.get(0).receivePercept(link.getSource(), ModuleName.SceneGraph);
		pamListeners.get(0).receivePercept((Node)link.getSink(),ModuleName.SceneGraph);
		pamListeners.get(0).receivePercept(link,ModuleName.SceneGraph);
		// 过阈值才通达？不通达不代表没有，无场景无语法=不可能生成=除非直接回忆现有
		pamListeners.get(0).receivePercept(link.getSource(),ModuleName.CurrentSM);
		pamListeners.get(0).receivePercept((Node)link.getSink(), ModuleName.CurrentSM);
		pamListeners.get(0).receivePercept(link, ModuleName.CurrentSM);
		// 无意识痕迹
		pamListeners.get(0).receivePercept(link.getSource(),ModuleName.NonGraph);
		pamListeners.get(0).receivePercept((Node)link.getSink(), ModuleName.NonGraph);
		pamListeners.get(0).receivePercept(link, ModuleName.NonGraph);

		// 从边类型开始激活
		linkable = getNode(retype);

		if (linkable == null) {
			linkable = pamNodeStructure.getNeoNode(retype);
			if (linkable != null) {
				addDefaultNode((Node) linkable);
			}
		}
		linkable.setActivation(0.8);
		// 直接从场景激活语法
		propagateActivationToParents((Node) linkable,1, "sentence");
	}

	private void SetAct(Node sink, int lofssize, String pcate) {
        // 多个条件约束加入意识，过阈值=非单边+非存在+累积，意象，存在则让衰减减慢，否则不管
        // 刺激重复=加速衰减，刺激太少=触发无聊感，刺激太多=设法稳定
        // 直接操作进出csm，联盟被架空，广播也失去意义？
	    boolean iscontain = false;
        if (nonNs.containsNode(sink)) {
            iscontain = true;
        }
        switch (pcate){// todo 激励应该来自注意调控，
            case "欲求":
                if (iscontain) {
                    sink.setActivation(sink.getActivation() + 0.009);
                }
                break;
            case "计划":
                if (iscontain) {
                    sink.setActivation(sink.getActivation() + 0.008);
                }
                break;
            case "时序":
                if (iscontain) {
                    sink.setActivation(sink.getActivation() + 0.007);
                }
                break;
            case "顺承":
                if (iscontain) {
                    sink.setActivation(sink.getActivation() + 0.005);
                }
                break;
            case "子类":
                if (iscontain) {
                    sink.setActivation(sink.getActivation() + 0.006);
                }
                break;
            case "内容":
                if (iscontain) {
                    sink.setActivation(sink.getActivation() + 0.007);
                }
                break;
            case "意图":
                if (iscontain) {
                    sink.setActivation(sink.getActivation() + 0.008);
                }
                break;
           default:
                if (iscontain) {
                    sink.setActivation(sink.getActivation() + 0.004);
                }
                break;
        }

//        if (nonNs.containsNode(sink)) {
//            if(lofssize == 1){
//                sink.setActivation(sink.getActivation() + 0.002);
//            }else {
//                // 异边激活更大，同一条激活小
//                sink.setActivation(sink.getActivation() + 0.005);
//            }
//			if(!isExists){
////			sink.setActivation(sink.getActivation() + pnact*0.02);
//			}else {
//
//			}
//        }

    }

    // 海马，中短期到长期记忆，睡前是中期到长期？
	private class LongMemBackgroundTask extends FrameworkTaskImpl {
		public LongMemBackgroundTask(int ticksPerRun) {
			super(ticksPerRun);
		}
		@Override
		protected void runThisFrameworkTask() {
			if(attemptLongMemory() != null){
				setNextTicksPerRun(150);
//				candidateThreshold = maxActivationThreshold;
			}else{
//				candidateThreshold -= thresholdDecayRate;
//				if(candidateThreshold < 0.0){
//					candidateThreshold=0.0;
//				}
			}
		}
	}

	private Node attemptLongMemory() {
		Node node = new NodeImpl();
		return null;
	}

	private int getCurrentstate(int currentstate0, int exsittruth) {
		int currentstate = 0;
		if (currentstate0 == 0) {
			switch (exsittruth){
				case 0:	// 0为虚
					currentstate = 0;
					break;
				case 1:	// 1为实
					currentstate = 2; // 实先虚后
					break;
				case 2:	// 实先虚后
					currentstate = 2;
					break;
				case 3:	//虚先实后
					currentstate = 4; //多层+虚后
					break;
				case 4:	//多层+虚后
					currentstate = 4;
					break;
				case 5:	//多层+实后
					currentstate = 4;
					break;
				default:break;
			}
		}else {
			switch (exsittruth){
				case 0:	// 0为虚
					currentstate = 3;	//虚先实后
					break;
				case 1:	// 1为实
					currentstate = 1;
					break;
				case 2:	// 实先虚后
					currentstate = 5;	//多层+实后
					break;
				case 3:	//虚先实后
					currentstate = 3;	//虚先实后
					break;
				case 4:	//多层+虚后
					currentstate = 5;	//多层+实后
					break;
				case 5:	//多层+实后
					currentstate = 5;	//多层+实后
					break;
				default:break;
			}
		}
		return currentstate;
	}

	// 场景核心都实际发生，场景为实
	private int getCurrentstate(String pname, int exsittruth, boolean exsit, boolean isstate){
		int currentstate = 0;
		boolean isact = false;
		boolean isto = false;
		boolean isactreal = false;
		boolean istoreal = false;
		String linkcate;
		for(Link link : csmNs.getLinks()){
			if (link.getSink().getName().equals(pname)) {
				linkcate = link.getCategory().getName();
				// csm显意识，有则为实？
				int truth = link.getSource().getTruth();
				if(truth == 1 || truth == 3 || truth == 5){
					if (linkcate.equals("受事")) {
						istoreal = true;
					}else if(linkcate.equals("动作")){
						isactreal = true;
					}
				}
			}
		}
		int cores = 1;
		if(isstate){
			cores = (int) AgentStarter.statemap.get(pname);
		}else {
			cores = (int) AgentStarter.actmap.get(pname);
		}
		if(!exsit){
			// 只有一个核心的话，可能为实，其他多核心肯定为虚。
			if(isactreal && cores == 1){
				currentstate = 1;
			}
		}else {
			if (cores == 1) {// 只要核心不实，就肯定虚 = 0
				if (isactreal) {
					currentstate = getCurrentstate(1, exsittruth);
				} else {
					currentstate = getCurrentstate(0, exsittruth);
				}
			} else if (cores == 2) {
				if (isactreal && istoreal) {
					currentstate = getCurrentstate(1, exsittruth);
				} else {
					currentstate = getCurrentstate(0, exsittruth);
				}
			} else if (cores == 3) {
			}
		}

		return currentstate;
	}

	/**
	 * Propagates specified activation from specified source along specified link.
	 * param src the source of the activation
	 * 从指定的源沿着指定的链接传播指定的激活。参数 src 激活源
	 * @param link the {@link PamLink} to propagate the activation down.
	 * @param activation amount of activation coming from the source. amountToPropagate
	 */
	protected void propagateActivation(Linkable src, PamLink link, double activation, int deep, String from) {
//		if (logger.isLoggable(Level.FINEST)) {
//			logger.log(Level.FINEST,
//					"Exciting sink: {1} and connecting link {2} amount: {3}",
//					new Object[]{TaskManager.getCurrentTick(),link.getSink(),link,activation});
//		}

		// 全部元组化？启发式传播逐个传，按需组合查询，双管齐下，线程执行，时刻跟踪注意力，也便于注意调控
		// 筛选机制避免大量图数据处理，用不着复杂查询，但复杂查询都是主动搜索=非启发式，
		// 注意力是线程调控=不管搜索类型，总之是要查+链式+灵活+高效，
		// 新建派生点边，另外处理，不进行大图传播？可进行WM子图传播，与基底相关的非皮层线程、存取不纳入调控=也难调控=含海马
		// 全拆=低命中+低效率+高能耗+高内存，只为极小的可能利用率=中间数据过多+过杂，不经济+不擅长
		// nars长句可不拆分查询，推理可保留长句，保存时要命名和拆分，模式子图整体查+整体存
		PropagationTask task = new PropagationTask(propagationTaskTicksPerRun, link, activation, this, deep, from);
		taskSpawner.addTask(task);
	}
	
	@Override
	public void addToPercept(NodeStructure ns) {

		ObjectContainer container = getObjectContainer();

		ns = convertNodeStructure(ns);
		ns.setSceneSite(container.toString());
		ns.setSceneTime(String.valueOf(TaskManager.getCurrentTick()));

		for (PamListener pl : pamListeners) {
			pl.receivePercept(ns);
		}
	}

	private ObjectContainer getObjectContainer() {
		ALifeWorld world = (ALifeWorld) environment.getModuleContent();
		ALifeObject agent = world.getObject("agent");
		return agent.getContainer();
	}

	private NodeStructure convertNodeStructure( NodeStructure ns) {
		NodeStructure convertedNS = new NodeStructureImpl();
		String convertedType=null;
		for (Node n: ns.getNodes()) {
			convertedType=typeConversionMap.get(n.getFactoryType());
			if(convertedType==null){
				convertedType=factory.getDefaultNodeType();
			}
			n.setActivation(n.getTotalActivation());
			convertedNS.addNode(n, convertedType);
		}
		for (Link l: ns.getLinks()) {
			if (l.isSimpleLink()) {
				convertedType = typeConversionMap.get(l.getFactoryType());
				if(convertedType==null){
					convertedType=factory.getDefaultLinkType();
				}
				l.setActivation(l.getTotalActivation());
				convertedNS.addLink(l, convertedType);
			}
		}
		for (Link l: ns.getLinks()) {
			if (!l.isSimpleLink()) {
				convertedType = typeConversionMap.get(l.getFactoryType());
				if(convertedType==null){
					convertedType=factory.getDefaultLinkType();
				}
				l.setActivation(l.getTotalActivation());
				convertedNS.addLink(l, convertedType);
			}
		}
		return convertedNS;
	}

	@Override
	public void addToPercept(Link l) {
		Link converted = convertLink(l);
		for (PamListener pl : pamListeners) {
			pl.receivePercept(converted);
		}
	}
	
	private Link convertLink( Link l) {
		String convertedType = typeConversionMap.get(l.getFactoryType());
		if(convertedType == null){
			convertedType=factory.getDefaultLinkType();
		}
		Link res = factory.getLink(convertedType,l.getSource(),
								   l.getSink(), l.getCategory(),
									l);
//		Link res = factory.getLink(l,"PamLinkImpl");
		res.setActivation(l.getTotalActivation());
		res.updateLinkValues(l);
		return res;
	}

	@Override
	public void addToPercept(Node n) {
		Node converted = convertNode(n);
		for (PamListener pl : pamListeners) {
			pl.receivePercept(converted);
		}
	}

	private Node convertNode(Node n) {
//		String convertedType = typeConversionMap.get(n.getFactoryType());
//		if(convertedType==null){
//			convertedType=factory.getDefaultNodeType();
//		}

		Node res = factory.getNode(n,"PamNodeImpl");
		res.setActivation(n.getTotalActivation());

		return res;
	}

	@Override
	public boolean containsNode(Node node) {
		return pamNodeStructure.containsNode(node);
	}

	@Override
	public boolean containsNode(ExtendedId id) {
		return pamNodeStructure.containsNode(id);
	}

	@Override
	public boolean containsLink(Link l) {
		return pamNodeStructure.containsLink(l);
	}

	@Override
	public boolean containsLink(ExtendedId id) {
		return pamNodeStructure.containsLink(id);
	}

	@Override
	public Collection<Node> getNodes() {
		return pamNodeStructure.getNodes();
	}

	@Override
	public Collection<Link> getLinks() {
		return pamNodeStructure.getLinks();
	}

	@Override
	public Object getModuleContent(Object... params) {
		return new UnmodifiableNodeStructureImpl(pamNodeStructure);
	}

	@Override
	public void addListener(ModuleListener l) {
		if (l instanceof PamListener) {
			addPamListener((PamListener) l);
		} else {
			logger.log(Level.WARNING,
					"Cannot add listener type {1} to this module.",
					new Object[] { TaskManager.getCurrentTick(), l });
		}
	}

	/**
	 * Returns the perceptThreshold
	 * @return threshold for a {@link PamLinkable} to be instantiated into a percept
	 */
	public static double getPerceptThreshold() {
		return perceptThreshold;
	}

	@Override
	public void setPerceptThreshold(double t) {
		if (t >= 0.0 && t <= 1.0) {
			PAMemoryImpl.perceptThreshold = t;
		} else {
			logger.log(Level.WARNING,
							"Percept threshold must in range [0.0, 1.0]. Threshold will not be modified.",
							TaskManager.getCurrentTick());
		}
	}

	@Override
	public boolean isOverPerceptThreshold( Linkable l) {
//		return l.getTotalActivation() > perceptThreshold;
		return (l.getTotalActivation()+l.getTotalIncentiveSalience())>getPerceptThreshold();
	}

	@Override
	public double getUpscaleFactor() {
		return upscaleFactor;
	}

	@Override
	public void setUpscaleFactor(double f) {
		if (f < 0.0) {
			upscaleFactor = 0.0;
		} else if (f > 1.0) {
			upscaleFactor = 1.0;
		} else {
			upscaleFactor = f;
		}
	}

	@Override
	public double getDownscaleFactor() {
		return downscaleFactor;
	}

	@Override
	public void setDownscaleFactor(double f) {
		if (f < 0.0) {
			downscaleFactor = 0.0;
		} else if (f > 1.0) {
			downscaleFactor = 1.0;
		} else {
			downscaleFactor = f;
		}
	}

	@Override
	public Link getLink(ExtendedId eid) {
		return pamNodeStructure.getLink(eid);
	}

	@Override
	public Node getNode(ExtendedId eid) {
		return pamNodeStructure.getNode(eid);
	}

	@Override
	public Node getNode(int id) {
		return pamNodeStructure.getNode(id);
	}

	@Override
	public Collection<LinkCategory> getLinkCategories() {
		return Collections.unmodifiableCollection(linkCategories.values());
	}

	@Override
	public LinkCategory getLinkCategory(int id) {
		return linkCategories.get(id);
	}

	@Override
	public LinkCategory addLinkCategory(LinkCategory cat) {
		LinkCategory result = null;
		if (cat instanceof PamNode) {
			result = (LinkCategory) pamNodeStructure.addNode((Node) cat,
					DEFAULT_NONDECAYING_PAMNODE);
			linkCategories.put(cat.getNodeId(), cat);
			nodesByLabel.put(cat.getName(),(PamNode) cat);
		}
		return result;
	}

	/*
	 * Adds a PamNode LinkCategory to the Pam's NodeStructure. LinkCategory is
	 * added directly and is not copied when added.
	 * 将PamNode LinkCategory添加到Pam的NodeStructure。 *直接添加LinkCategory，添加时不复制
	 *
	 * @param cat LinkCategory to add
	 * @return stored LinkCategory
	 */
	private LinkCategory addInternalLinkCategory(LinkCategory cat) {
		LinkCategory result = null;
		if (cat instanceof PamNode) {
			result = (LinkCategory) pamNodeStructure.addNode((Node) cat, false);
			linkCategories.put(cat.getNodeId(), cat);
		}
		return result;
	}

	/**
	 * Internal implementation of {@link NodeStructureImpl}. Allows {@link Node}
	 * to be added without copying them. 添加而不复制它们
	 */
	public static class PamNodeStructure extends NodeStructureImpl {
		/**
		 * @param nodeType
		 *            Default node type
		 * @param linkType
		 *            Default link type
		 */
		public PamNodeStructure(String nodeType, String linkType) {
			super(nodeType, linkType);
		}

		@Override
		public Node addNode(Node n, boolean copy) {
			return super.addNode(n, copy);
		}
	}

	@Override
	public Node getNode(String label) {
		return nodesByLabel.get(label);// 激活值可视化用
//		return getNode(label);
	}

	@Override
	public synchronized void receiveWorkspaceContent(ModuleName n, WorkspaceContent c) {
		// Todo 知觉联想记忆反馈
	}
	@Override
	public synchronized void receivePreafference(NodeStructure addList,NodeStructure deleteList) {
	}

	@Override
	public PamListener getListener(){
		return pamListeners.get(0);
	}
}
