package ontologybuilder;

// Common Libraries
import java.io.File;
import java.util.*;
import java.io.IOException;

// BPMN Parser Libraries
import org.camunda.bpm.model.xml.instance.ModelElementInstance;
import org.camunda.bpm.model.xml.type.ModelElementType;
import org.camunda.bpm.model.bpmn.Bpmn;
import org.camunda.bpm.model.bpmn.BpmnModelInstance;
import org.camunda.bpm.model.bpmn.impl.instance.Incoming;
import org.camunda.bpm.model.bpmn.impl.instance.Outgoing;
import org.camunda.bpm.model.bpmn.instance.EndEvent;
import org.camunda.bpm.model.bpmn.instance.ExclusiveGateway;
import org.camunda.bpm.model.bpmn.instance.ParallelGateway;
import org.camunda.bpm.model.bpmn.instance.StartEvent;
import org.camunda.bpm.model.bpmn.instance.Process;
import org.camunda.bpm.model.bpmn.instance.SubProcess;
import org.camunda.bpm.model.bpmn.instance.Task;

// Owl API Libraries
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.util.DefaultPrefixManager;

import org.semanticweb.owlapi.model.*;

public class DiagramParserC {
	List<ModelElementInstance> visitedNodes = new LinkedList<>();
	int subprocessIndex = 0;
	int joinIndex = 0;
	String projectname = "";
	String proyectPath = "";
	
	
	private void extractOntologyFromDiagram(OWLDataFactory dataFactory, PrefixManager prefixManager,
			OWLOntologyManager owlOntologyManager, OWLOntology currentOntology) {
		
		// Read a model from a file
		String fileName = "Choice";
		String fullFileName = this.proyectPath;
		File file = new File(fullFileName);
		BpmnModelInstance modelInstance = Bpmn.readModelFromFile(file);
		
		// Retrieve the start nodes of the diagram
		ModelElementType startType = modelInstance.getModel().getType(StartEvent.class);
		Collection<ModelElementInstance> startInstances = modelInstance.getModelElementsByType(startType);

		ModelElementType processType = modelInstance.getModel().getType(Process.class);
		Collection<ModelElementInstance> processInstances = modelInstance.getModelElementsByType(processType);
		ModelElementInstance mainProcess = ((List<ModelElementInstance>) processInstances).get(0);
		Collection<ModelElementInstance> mainStartInstances = mainProcess.getChildElementsByType(startType);
		mainStartInstances.retainAll(startInstances);
		
 		// Create the process class
 		OWLClass owlProcessClass = dataFactory.getOWLClass("#" + projectname, prefixManager);
 		OWLClass owlProcessSuperClass = dataFactory.getOWLClass("#" + projectname, prefixManager);
 		OWLSubClassOfAxiom subClassAxiom = dataFactory.getOWLSubClassOfAxiom(owlProcessClass, owlProcessSuperClass);
 		owlOntologyManager.applyChange(new AddAxiom(currentOntology, subClassAxiom));		
 		
 		// Instantiate the individual of the class
 		String processNameLower = projectname.substring(0, 1).toLowerCase() + projectname.substring(1) + "Process";
 		OWLIndividual process = dataFactory.getOWLNamedIndividual("#" + processNameLower.replace(" ",""), prefixManager);
 		OWLClassAssertionAxiom classAssertionAxiom = dataFactory.getOWLClassAssertionAxiom(owlProcessClass, process);
 		owlOntologyManager.applyChange(new AddAxiom(currentOntology, classAssertionAxiom));
 		
		 
		OWLIndividual start = dataFactory.getOWLNamedIndividual("#" + "start0", prefixManager);				
		OWLObjectProperty beginsWith = dataFactory.getOWLObjectProperty("#" + "beginsWith0", prefixManager);
				
		OWLObjectPropertyAssertionAxiom assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(beginsWith, process, start);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));				
		OWLClass owlStartClass = dataFactory.getOWLClass("#" + "Start", prefixManager);
		
		LinkedList<Integer> subIndex = new LinkedList<>();
 		subIndex.add(0);
		
		if (mainStartInstances.size() > 1) {
			// If there is more than one start node it builds a join between the 2 process
			Set<OWLClassExpression> expressionList = new HashSet<OWLClassExpression>();
			expressionList.add(owlStartClass);
			for (ModelElementInstance startNode: mainStartInstances) {
				OWLClassExpression nextNode = parseNextNode(process, start, startNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, 1, subIndex);		
				expressionList.add(nextNode);										
			}	
			
			// Make the definition for the process name
			OWLObjectProperty followedBy = dataFactory.getOWLObjectProperty("#" + "followedBy0", prefixManager);
			OWLClassExpression followedExactlyXNodes = dataFactory.getOWLObjectExactCardinality(expressionList.size() - 1, followedBy);
			expressionList.add(followedExactlyXNodes);
			OWLObjectIntersectionOf classExpresion = dataFactory.getOWLObjectIntersectionOf(expressionList);
			OWLEquivalentClassesAxiom equivalenceAxiom = dataFactory.getOWLEquivalentClassesAxiom(owlProcessClass, classExpresion);
			owlOntologyManager.applyChange(new AddAxiom(currentOntology, equivalenceAxiom));
		
		} else {
			assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(beginsWith, process, start);
			owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));
			
			OWLClassExpression nextNode = parseNextNode(process, start, ((List<ModelElementInstance>) mainStartInstances).get(0), modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, 1, subIndex);		
			
			// Make the definition for the process name
			OWLObjectIntersectionOf classExpresion = dataFactory.getOWLObjectIntersectionOf(owlStartClass, nextNode);
			OWLEquivalentClassesAxiom equivalenceAxiom = dataFactory.getOWLEquivalentClassesAxiom(owlProcessClass, classExpresion);
			owlOntologyManager.applyChange(new AddAxiom(currentOntology, equivalenceAxiom));		
		}
	}
	
	private OWLClassExpression parseNextNode(OWLIndividual process, OWLIndividual precededIndividual, ModelElementInstance startNode, BpmnModelInstance modelInstance, OWLDataFactory dataFactory,  PrefixManager prefixManager,
			OWLOntologyManager owlOntologyManager, OWLOntology currentOntology, int subIndexCount, LinkedList<Integer> subIndex) {

		String nodeId = null;
		String sequenceId = null;
		ModelElementInstance currentNode = null;
		OWLClassExpression returnNode = null;
        Set<OWLAxiom> domainsAndRanges = new HashSet<OWLAxiom>();
		OWLClass owlNodeClass = dataFactory.getOWLClass("#" + "Node", prefixManager);		
		OWLClass owlProcessClass = dataFactory.getOWLClass("#" + projectname, prefixManager);		
		OWLClass owlSubProcessClass = dataFactory.getOWLClass("#" + "SubProcess", prefixManager);		
		OWLObjectUnionOf classExpression = dataFactory.getOWLObjectUnionOf(owlSubProcessClass, owlProcessClass);
		
		String propertyIndex = subIndex.getFirst().toString();
		for (int i = 1; i < subIndexCount; i++) {
			propertyIndex = propertyIndex + "." + subIndex.get(i).toString();
		}
		
		OWLObjectProperty contains = dataFactory.getOWLObjectProperty("#" + "Contains" + propertyIndex, prefixManager);
		if (!currentOntology.containsObjectPropertyInSignature(contains.getIRI())) {
			OWLObjectProperty containsSuper = dataFactory.getOWLObjectProperty("#" + "Contains", prefixManager);
			OWLSubObjectPropertyOfAxiom containsAxiom = dataFactory.getOWLSubObjectPropertyOfAxiom(contains, containsSuper);
			owlOntologyManager.applyChange(new AddAxiom(currentOntology, containsAxiom));
			domainsAndRanges.add(dataFactory.getOWLObjectPropertyDomainAxiom(contains, classExpression));
			domainsAndRanges.add(dataFactory.getOWLObjectPropertyRangeAxiom(contains, owlNodeClass));
	        owlOntologyManager.addAxioms(currentOntology, domainsAndRanges);
		}
			
		OWLObjectProperty endsWith = dataFactory.getOWLObjectProperty("#" + "endsWith" + propertyIndex, prefixManager);
		if (!currentOntology.containsObjectPropertyInSignature(endsWith.getIRI())) {
			OWLObjectProperty endsWithSuper = dataFactory.getOWLObjectProperty("#" + "endsWith", prefixManager);
			OWLSubObjectPropertyOfAxiom endsWithAxiom = dataFactory.getOWLSubObjectPropertyOfAxiom(endsWith, endsWithSuper);
			owlOntologyManager.applyChange(new AddAxiom(currentOntology, endsWithAxiom));
			domainsAndRanges.add(dataFactory.getOWLObjectPropertyDomainAxiom(endsWith, classExpression));
			domainsAndRanges.add(dataFactory.getOWLObjectPropertyRangeAxiom(endsWith, owlNodeClass));
	        owlOntologyManager.addAxioms(currentOntology, domainsAndRanges);
		}
		
		OWLObjectProperty followedBy = dataFactory.getOWLObjectProperty("#" + "followedBy" + propertyIndex, prefixManager);
		if (!currentOntology.containsObjectPropertyInSignature(followedBy.getIRI())) {
			OWLObjectProperty followedBySuper = dataFactory.getOWLObjectProperty("#" + "followedBy", prefixManager);
			OWLSubObjectPropertyOfAxiom followedByAxiom = dataFactory.getOWLSubObjectPropertyOfAxiom(followedBy, followedBySuper);
			owlOntologyManager.applyChange(new AddAxiom(currentOntology, followedByAxiom));
			domainsAndRanges.add(dataFactory.getOWLObjectPropertyDomainAxiom(followedBy, owlNodeClass));
			domainsAndRanges.add(dataFactory.getOWLObjectPropertyRangeAxiom(followedBy, owlNodeClass));
	        owlOntologyManager.addAxioms(currentOntology, domainsAndRanges);
		}
		
		Collection<Outgoing> outgoingEdges = startNode.getChildElementsByType(Outgoing.class);
	
		// If there is only 1 child the current node is a task or an end
		if(outgoingEdges.size()== 1) {				
			sequenceId = startNode.getUniqueChildElementByType(Outgoing.class).getRawTextContent();
			nodeId = modelInstance.getModelElementById(sequenceId).getAttributeValue("targetRef");	
			currentNode = modelInstance.getModelElementById(nodeId);
			
			// If it is a task
			if (currentNode instanceof Task) {			
				returnNode =  getNextNodeExpresion(process, precededIndividual, currentNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, followedBy, contains, "TASK", null, subIndexCount, subIndex);
			}
		
			//if it reaches the end node
			if (currentNode instanceof EndEvent) {
				// Declare the assertion between the predecessor node
				OWLClass owlEndClass = dataFactory.getOWLClass("#" + "End", prefixManager);
				OWLIndividual end = dataFactory.getOWLNamedIndividual("#" + "end" + propertyIndex, prefixManager);
				OWLClassAssertionAxiom classAssertionAxiom = dataFactory.getOWLClassAssertionAxiom(owlEndClass, end);
				owlOntologyManager.applyChange(new AddAxiom(currentOntology, classAssertionAxiom));
				
				OWLObjectPropertyAssertionAxiom assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(followedBy, precededIndividual, end);
	            owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));

	            assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(endsWith, process, end);
	            owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));
           
	    		OWLClassExpression followedByExactly1Node = dataFactory.getOWLObjectExactCardinality(1, followedBy, dataFactory.getOWLClass("#" + "End", prefixManager));
				returnNode = followedByExactly1Node;	
			}
			
			// If it is a subprocess
			if (currentNode instanceof SubProcess) {
				returnNode =  getNextNodeExpresion(process, precededIndividual, currentNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, followedBy, contains, "SUBPROCESS", null, subIndexCount, subIndex);
			}

			// If it is a XOR
			if (currentNode instanceof ExclusiveGateway) {
				// If there is no task between the start node and the gateway
				if (startNode instanceof StartEvent) {
					returnNode = getExtraNextNodeExpression(process, precededIndividual, currentNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, followedBy, contains, "START", null, subIndexCount, subIndex);										
				} else {
					returnNode = parseNextNode(process, precededIndividual, currentNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, subIndexCount, subIndex);
				}
				
			}

			// If it is a AND
			if (currentNode instanceof ParallelGateway) {
				// If there is no task between the start node and the gateway
				if (startNode instanceof StartEvent) {
					returnNode = getExtraNextNodeExpression(process, precededIndividual, currentNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, followedBy, contains, "START", null, subIndexCount, subIndex);										
				}
				// If it is a AND-split
				else if (currentNode.getChildElementsByType(Incoming.class).size() == 1) {
					returnNode = parseNextNode(process, precededIndividual, currentNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, subIndexCount, subIndex);
				// If it is a AND-join
				} else {
					OWLClass owlJoinClass = dataFactory.getOWLClass("#" + "Join", prefixManager);
					
					OWLIndividual join = dataFactory.getOWLNamedIndividual("#" + "join" + joinIndex, prefixManager);

					if (visitedNodes.contains(currentNode)) {
						joinIndex++;
					} else {
						visitedNodes.add(currentNode);
					}
					
					OWLClassAssertionAxiom classAssertionAxiom = dataFactory.getOWLClassAssertionAxiom(owlJoinClass, join);
					owlOntologyManager.applyChange(new AddAxiom(currentOntology, classAssertionAxiom));
					
					// Declare the assertion between the process node
			        OWLObjectPropertyAssertionAxiom assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(contains, process, join);
			        owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));
			
					// Declare the assertion between the predecessor node
			        assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(followedBy, precededIndividual, join);
			        owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));
					
					returnNode = parseNextNode(process, join, currentNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, subIndexCount, subIndex);										
					OWLObjectIntersectionOf classExpresion = dataFactory.getOWLObjectIntersectionOf(owlJoinClass, returnNode);
					OWLClassExpression followedByExactly1Node = dataFactory.getOWLObjectExactCardinality(1, followedBy, classExpresion);
					returnNode = followedByExactly1Node;
				}	
			}

		// If there is more than 1 child the current node is a split
		} else {	
			Set<OWLClassExpression> nodeList = new HashSet<>();
			
			for (ModelElementInstance each: outgoingEdges) {
			
				nodeId = modelInstance.getModelElementById(each.getRawTextContent()).getAttributeValue("targetRef");
				currentNode = modelInstance.getModelElementById(nodeId);
				String type = "";

				// if is XOR or AND
				if (currentNode instanceof ExclusiveGateway || currentNode instanceof ParallelGateway) {
					if (startNode instanceof ExclusiveGateway) {
						returnNode = getExtraNextNodeExpression(process, precededIndividual, currentNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, followedBy, contains, "XOR", each, subIndexCount, subIndex);																
					// OR currentNode ??
					} else if (startNode instanceof ParallelGateway) {
						returnNode = getExtraNextNodeExpression(process, precededIndividual, currentNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, followedBy, contains, "AND", each, subIndexCount, subIndex);															
					}
				} else {
					if (startNode instanceof ExclusiveGateway) {
						type = "XOR";
					} else {
						type = "AND";
					}
					
					// If it is a task
					if (currentNode instanceof Task) {			
						returnNode =  getNextNodeExpresion(process, precededIndividual, currentNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, followedBy, contains, type, each, subIndexCount, subIndex);
					}
					//if it reaches the end node
					else if (currentNode instanceof EndEvent) {
						// Declare the assertion between the predecessor node
						OWLClass owlEndClass = dataFactory.getOWLClass("#" + "End", prefixManager);
						OWLIndividual end = dataFactory.getOWLNamedIndividual("#" + "end" + propertyIndex, prefixManager);
						OWLClassAssertionAxiom classAssertionAxiom = dataFactory.getOWLClassAssertionAxiom(owlEndClass, end);
						owlOntologyManager.applyChange(new AddAxiom(currentOntology, classAssertionAxiom));
						
						OWLObjectPropertyAssertionAxiom assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(followedBy, precededIndividual, end);
			            owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));

			            assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(endsWith, process, end);
			            owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));
		           
			    		OWLClassExpression followedByExactly1Node = dataFactory.getOWLObjectExactCardinality(1, followedBy, dataFactory.getOWLClass("#" + "End", prefixManager));
						returnNode = followedByExactly1Node;	
					}
					// If it is a subprocess
					if (currentNode instanceof SubProcess) {
						returnNode =  getNextNodeExpresion(process, precededIndividual, currentNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, followedBy, contains, type, each, subIndexCount, subIndex);
					}

					
					
				}
									
				nodeList.add(returnNode);
			}	
			
			if (startNode instanceof ExclusiveGateway) {				
		    	OWLObjectUnionOf classExpresion = dataFactory.getOWLObjectUnionOf(nodeList);
		    	returnNode = classExpresion;
			// Is an AND gateway
			} else {
				OWLClassExpression followedExactlyXNodes = dataFactory.getOWLObjectExactCardinality(nodeList.size(), followedBy);
				nodeList.add(followedExactlyXNodes);
		    	OWLObjectIntersectionOf classExpresion = dataFactory.getOWLObjectIntersectionOf(nodeList);
		    	returnNode = classExpresion;				
			}
			
			
		}

		return returnNode;
	}

	
	private OWLClassExpression getExtraNextNodeExpression(OWLIndividual process, OWLIndividual precededIndividual, ModelElementInstance currentNode, BpmnModelInstance modelInstance, OWLDataFactory dataFactory,  PrefixManager prefixManager,
			OWLOntologyManager owlOntologyManager, OWLOntology currentOntology, OWLObjectProperty followedBy, OWLObjectProperty contains, String nodeType, ModelElementInstance outgoingEdge, int subIndexCount, LinkedList<Integer> subIndex) {
		
		OWLClassExpression returnNode;
		boolean ret = false;
		
		// Make the concept task class
		OWLClass owlConceptClass = dataFactory.getOWLClass("#" + "ConceptGeneric", prefixManager);		
		
		String suffix = "";
		int i = 2;
		if (currentOntology.containsClassInSignature(owlConceptClass.getIRI())) {	
			if (!visitedNodes.contains(currentNode)) {
				while (currentOntology.containsClassInSignature(owlConceptClass.getIRI())) {
					owlConceptClass = dataFactory.getOWLClass("#" + "ConceptGeneric" + i, prefixManager);	
					i++;
				}
				suffix += i - 1;
				visitedNodes.add(currentNode);
			} else {
				ret = true;
			}
		} else {
			visitedNodes.add(currentNode);
		}
				
		if (nodeType == "AND") {
			OWLClassExpression followedBySomeNode = dataFactory.getOWLObjectSomeValuesFrom(followedBy, owlConceptClass);
			returnNode = followedBySomeNode;
		} else {
			OWLClassExpression followedByExactly1Node = dataFactory.getOWLObjectExactCardinality(1, followedBy, owlConceptClass);
			returnNode = followedByExactly1Node;			
		}
		
		if (ret) {
			return returnNode;
		}
		
		OWLDeclarationAxiom conceptActClassAxiom = dataFactory.getOWLDeclarationAxiom(owlConceptClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, conceptActClassAxiom));            
		
		OWLClass owlConceptActClass = dataFactory.getOWLClass("#" + "ConceptActivity", prefixManager);			
		OWLSubClassOfAxiom subClassAxiom = dataFactory.getOWLSubClassOfAxiom(owlConceptClass, owlConceptActClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, subClassAxiom));
		
		// Instantiate the individual of the class
		OWLIndividual task = dataFactory.getOWLNamedIndividual("#" + "genericTask" + i, prefixManager);
		OWLClass owlTaskClass = dataFactory.getOWLClass("#" + "Task", prefixManager);			
		OWLClassAssertionAxiom classAssertionAxiom = dataFactory.getOWLClassAssertionAxiom(owlTaskClass, task);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, classAssertionAxiom));
		
		// Declare the assertion between the process node
        OWLObjectPropertyAssertionAxiom assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(contains, process, task);
        owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));
		
		// Declare the assertion between the predecessor node
        assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(followedBy, precededIndividual, task);
        owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));
        
		OWLClassExpression nextNode = parseNextNode(process, task, currentNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, subIndexCount, subIndex);	
		
		if (nodeType == "XOR") {
			OWLDataProperty pairsWithProperty = dataFactory.getOWLDataProperty("#" + "pairsWith", prefixManager);
			
			String pairValue = modelInstance.getModelElementById(outgoingEdge.getRawTextContent()).getAttributeValue("name");
			if (pairValue == null) {
				pairValue = "";
			}
	        OWLDataPropertyAssertionAxiom assertionData = dataFactory.getOWLDataPropertyAssertionAxiom(pairsWithProperty, task, pairValue);
	        owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertionData));
	        
	        OWLDatatype string = dataFactory.getOWLDatatype("xsd:string", prefixManager);
			
			OWLClassExpression pairsWithSomeString = dataFactory.getOWLDataSomeValuesFrom(pairsWithProperty, string);

	        nextNode = dataFactory.getOWLObjectIntersectionOf(nextNode, pairsWithSomeString);
		}
		
		OWLObjectIntersectionOf classExpresion = dataFactory.getOWLObjectIntersectionOf(owlTaskClass, nextNode);
		OWLEquivalentClassesAxiom equivalenceAxiom = dataFactory.getOWLEquivalentClassesAxiom(owlConceptClass, classExpresion);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, equivalenceAxiom));
		
		return returnNode;		

	}
	
	
	private OWLClassExpression getNextNodeExpresion(OWLIndividual process, OWLIndividual precededIndividual, ModelElementInstance currentNode, BpmnModelInstance modelInstance, OWLDataFactory dataFactory,  PrefixManager prefixManager,
			OWLOntologyManager owlOntologyManager, OWLOntology currentOntology, OWLObjectProperty followedBy, OWLObjectProperty contains, String nodeType, ModelElementInstance outgoingEdge, int subIndexCount, LinkedList<Integer> subIndex) {
				
		boolean ret = false;
		boolean subProcessNode = false;
		
		String taskName = currentNode.getAttributeValue("name").replace(" ","");
		taskName = taskName.replaceAll("(\\r|\\n|\\r\\n)+", "");
		taskName = taskName.replaceAll("[(]", "");
		taskName = taskName.replaceAll("[)]", "");
		taskName = taskName.replaceAll(",", "_");
		OWLClassExpression returnNode;
		
		// Make the concept task class
		String taskNameUpper = taskName.substring(0, 1).toUpperCase() + taskName.substring(1);
		OWLClass owlConceptClass = dataFactory.getOWLClass("#" + "Concept" + taskNameUpper, prefixManager);
		
		String suffix = "";
		int i = 2;
		if (currentOntology.containsClassInSignature(owlConceptClass.getIRI())) {	
			if (!visitedNodes.contains(currentNode)) {
				while (currentOntology.containsClassInSignature(owlConceptClass.getIRI())) {
					owlConceptClass = dataFactory.getOWLClass("#" + "Concept" + taskNameUpper + i, prefixManager);	
					i++;
				}
				suffix += i - 1;
			} else {
				ret = true;
			}
		} else {
			visitedNodes.add(currentNode);
		}
		
		if (nodeType == "AND") {
			OWLClassExpression followedBySomeNode = dataFactory.getOWLObjectSomeValuesFrom(followedBy, owlConceptClass);
			returnNode = followedBySomeNode;
		} else {
			OWLClassExpression followedByExactly1Node = dataFactory.getOWLObjectExactCardinality(1, followedBy, owlConceptClass);
			returnNode = followedByExactly1Node;			
		}
		
		if (ret) {
			return returnNode;
		}
		
		OWLDeclarationAxiom conceptActClassAxiom = dataFactory.getOWLDeclarationAxiom(owlConceptClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, conceptActClassAxiom));            
		
		OWLClass owlConceptActClass = dataFactory.getOWLClass("#" + "ConceptActivity", prefixManager);			
		OWLSubClassOfAxiom subClassAxiom = dataFactory.getOWLSubClassOfAxiom(owlConceptClass, owlConceptActClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, subClassAxiom));
		
		OWLIndividual task = null;
		OWLClass owlTaskClass = null;
		
		if (!(currentNode instanceof SubProcess)) {
			// Instantiate the individual of the class
			String taskNameLower = taskName.substring(0, 1).toLowerCase() + taskName.substring(1) + suffix;
			task = dataFactory.getOWLNamedIndividual("#" + taskNameLower, prefixManager);
			owlTaskClass = dataFactory.getOWLClass("#" + "Task", prefixManager);			
			OWLClassAssertionAxiom classAssertionAxiom = dataFactory.getOWLClassAssertionAxiom(owlTaskClass, task);
			owlOntologyManager.applyChange(new AddAxiom(currentOntology, classAssertionAxiom));
			
			// Declare the assertion between the process node
	        OWLObjectPropertyAssertionAxiom assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(contains, process, task);
	        owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));
	
			// Declare the assertion between the predecessor node
	        assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(followedBy, precededIndividual, task);
	        owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));
		} else {
			subProcessNode = true;
			// Instantiate the individual of the subprocess
			String taskNameLower = taskName.substring(0, 1).toLowerCase() + taskName.substring(1) + "Process";
			task = dataFactory.getOWLNamedIndividual("#" + taskNameLower, prefixManager);

			if(subIndex.size() == subIndexCount) {
				subIndex.add(0);
			} else {
				int aux = subIndex.removeLast();
				aux++;
				subIndex.add(aux);
			}
			
			owlTaskClass = getSubProcess(taskNameUpper, task, currentNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, subIndexCount, subIndex);
			OWLClassAssertionAxiom classAssertionAxiom = dataFactory.getOWLClassAssertionAxiom(owlTaskClass, task);
			owlOntologyManager.applyChange(new AddAxiom(currentOntology, classAssertionAxiom));
			
			if (subIndex.size() > subIndexCount + 1)
				subIndex.removeLast();
			
			// Declare the assertion between the process node
	        OWLObjectPropertyAssertionAxiom assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(contains, process, task);
	        owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));
	
			// Declare the assertion between the predecessor node
	        assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(followedBy, precededIndividual, task);
	        owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));			
		}
		
		OWLClassExpression nextNode = parseNextNode(process, task, currentNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, subIndexCount, subIndex);
		
		if (nodeType.equals("XOR")) {
			OWLDataProperty pairsWithProperty = dataFactory.getOWLDataProperty("#" + "pairsWith", prefixManager);
			
			String pairValue = modelInstance.getModelElementById(outgoingEdge.getRawTextContent()).getAttributeValue("name");
			if (pairValue == null) {
				pairValue = "";
			}
	        OWLDataPropertyAssertionAxiom assertionData = dataFactory.getOWLDataPropertyAssertionAxiom(pairsWithProperty, task, pairValue);
	        owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertionData));
	        
	        OWLDatatype string = dataFactory.getOWLDatatype("xsd:string", prefixManager);
			
			OWLClassExpression pairsWithSomeString = dataFactory.getOWLDataSomeValuesFrom(pairsWithProperty, string);

	        nextNode = dataFactory.getOWLObjectIntersectionOf(nextNode, pairsWithSomeString);
		}
		
		OWLObjectIntersectionOf classExpresion = dataFactory.getOWLObjectIntersectionOf(owlTaskClass, nextNode);
		
		OWLEquivalentClassesAxiom equivalenceAxiom = dataFactory.getOWLEquivalentClassesAxiom(owlConceptClass, classExpresion);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, equivalenceAxiom));
		
		if (!subProcessNode) {		
			OWLIndividual task0 = dataFactory.getOWLNamedIndividual("#" + taskName.substring(0, 1).toLowerCase() + taskName.substring(1), prefixManager);
			OWLSameIndividualAxiom sameAsAxiom = dataFactory.getOWLSameIndividualAxiom(task0, task);
			owlOntologyManager.applyChange(new AddAxiom(currentOntology, sameAsAxiom));
		}
					
		return returnNode;		
	}
	
	public OWLClass getSubProcess(String name, OWLIndividual process, ModelElementInstance currentNode, BpmnModelInstance modelInstance, OWLDataFactory dataFactory,  PrefixManager prefixManager,
			OWLOntologyManager owlOntologyManager, OWLOntology currentOntology, int subIndexCount, LinkedList<Integer> subIndex) {

		subIndexCount++;

		String propertyIndex = subIndex.getFirst().toString();
		for (int i = 1; i < subIndexCount; i++) {
			propertyIndex = propertyIndex + "." + subIndex.get(i).toString();
		}
		

		OWLClass owlConceptSubProcessClass = dataFactory.getOWLClass("#" + name + "Process", prefixManager);			

		OWLClass owlSubProcessClass = dataFactory.getOWLClass("#" + "SubProcess", prefixManager);

		OWLSubClassOfAxiom subClassAxiom = dataFactory.getOWLSubClassOfAxiom(owlConceptSubProcessClass, owlSubProcessClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, subClassAxiom));
        
		// Retrieve the start nodes of the diagram
		ModelElementType startType = modelInstance.getModel().getType(StartEvent.class);
		Collection<ModelElementInstance> startInstances = modelInstance.getModelElementsByType(startType);
		
		ModelElementInstance mainProcess = currentNode;
		Collection<ModelElementInstance> mainStartInstances = mainProcess.getChildElementsByType(startType);
		mainStartInstances.retainAll(startInstances);

		OWLIndividual start = dataFactory.getOWLNamedIndividual("#" + "start" + propertyIndex, prefixManager);
		OWLObjectProperty beginsWith = dataFactory.getOWLObjectProperty("#" + "beginsWith" + propertyIndex, prefixManager);
		OWLObjectProperty beginsWithSuper = dataFactory.getOWLObjectProperty("#" + "beginsWith", prefixManager);
		OWLSubObjectPropertyOfAxiom beginsWithAxiom = dataFactory.getOWLSubObjectPropertyOfAxiom(beginsWith, beginsWithSuper);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, beginsWithAxiom));
		
	    Set<OWLAxiom> domainsAndRanges = new HashSet<OWLAxiom>();
		OWLClass owlProcessClass = dataFactory.getOWLClass("#" + projectname, prefixManager);		
		OWLClass owlNodeClass = dataFactory.getOWLClass("#" + "Node", prefixManager);		
		OWLObjectUnionOf classExpression = dataFactory.getOWLObjectUnionOf(owlSubProcessClass, owlProcessClass);
	
		domainsAndRanges.add(dataFactory.getOWLObjectPropertyDomainAxiom(beginsWith, classExpression));
		domainsAndRanges.add(dataFactory.getOWLObjectPropertyRangeAxiom(beginsWith, owlNodeClass));
        owlOntologyManager.addAxioms(currentOntology, domainsAndRanges);
		
		OWLObjectPropertyAssertionAxiom assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(beginsWith, process, start);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));				
		OWLClass owlStartClass = dataFactory.getOWLClass("#" + "Start", prefixManager);
		
		if (mainStartInstances.size() > 1) {
			// If there is more than one start node it builds a join between the 2 process
			Set<OWLClassExpression> expressionList = new HashSet<OWLClassExpression>();
			expressionList.add(owlStartClass);
			for (ModelElementInstance startNode: mainStartInstances) {
				OWLClassExpression nextNode = parseNextNode(process, start, startNode, modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, subIndexCount, subIndex);		
				expressionList.add(nextNode);										
			}	
			
			// Make the definition for the process name
			OWLObjectProperty followedBy = dataFactory.getOWLObjectProperty("#" + "followedBy0", prefixManager);
			OWLClassExpression followedExactlyXNodes = dataFactory.getOWLObjectExactCardinality(expressionList.size() - 1, followedBy);
			expressionList.add(followedExactlyXNodes);
			OWLObjectIntersectionOf classExpresion = dataFactory.getOWLObjectIntersectionOf(expressionList);
			OWLEquivalentClassesAxiom equivalenceAxiom = dataFactory.getOWLEquivalentClassesAxiom(owlConceptSubProcessClass, classExpresion);
			owlOntologyManager.applyChange(new AddAxiom(currentOntology, equivalenceAxiom));
		
		} else {
			assertion = dataFactory.getOWLObjectPropertyAssertionAxiom(beginsWith, process, start);
			owlOntologyManager.applyChange(new AddAxiom(currentOntology, assertion));
			
			OWLClassExpression nextNode = parseNextNode(process, start, ((List<ModelElementInstance>) mainStartInstances).get(0), modelInstance, dataFactory, prefixManager, owlOntologyManager, currentOntology, subIndexCount, subIndex);		
			
			// Make the definition for the process name
			OWLObjectIntersectionOf classExpresion = dataFactory.getOWLObjectIntersectionOf(owlStartClass, nextNode);
			OWLEquivalentClassesAxiom equivalenceAxiom = dataFactory.getOWLEquivalentClassesAxiom(owlConceptSubProcessClass, classExpresion);
			owlOntologyManager.applyChange(new AddAxiom(currentOntology, equivalenceAxiom));		
		}

		return owlConceptSubProcessClass;		
	}

	
	private void generateBaseDiagramOntology(OWLDataFactory dataFactory, PrefixManager prefixManager,
			OWLOntologyManager owlOntologyManager, OWLOntology currentOntology) {

		// Declares basic diagram classes an its subclasses	
		OWLClass owlProcessClass = dataFactory.getOWLClass("#" + projectname, prefixManager);
		
		OWLClass owlConceptActClass = dataFactory.getOWLClass("#" + "ConceptActivity", prefixManager);
		OWLDeclarationAxiom conceptActClassAxiom = dataFactory.getOWLDeclarationAxiom(owlConceptActClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, conceptActClassAxiom));

		OWLClass owlNodeClass = dataFactory.getOWLClass("#" + "Node", prefixManager);
		OWLDeclarationAxiom nodeClassAxiom = dataFactory.getOWLDeclarationAxiom(owlNodeClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, nodeClassAxiom));

		OWLClass owlTaskClass = dataFactory.getOWLClass("#" + "Task", prefixManager);
		OWLDeclarationAxiom taskClassAxiom = dataFactory.getOWLDeclarationAxiom(owlTaskClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, taskClassAxiom));

		OWLClass owlStartClass = dataFactory.getOWLClass("#" + "Start", prefixManager);
		OWLDeclarationAxiom startClassAxiom = dataFactory.getOWLDeclarationAxiom(owlStartClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, startClassAxiom));

		OWLClass owlEndClass = dataFactory.getOWLClass("#" + "End", prefixManager);
		OWLDeclarationAxiom endClassAxiom = dataFactory.getOWLDeclarationAxiom(owlEndClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, endClassAxiom));

		OWLClass owlJoinClass = dataFactory.getOWLClass("#" + "Join", prefixManager);
		OWLDeclarationAxiom joinClassAxiom = dataFactory.getOWLDeclarationAxiom(owlJoinClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, joinClassAxiom));
		
		OWLSubClassOfAxiom subClassAxiom = dataFactory.getOWLSubClassOfAxiom(owlStartClass, owlNodeClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, subClassAxiom));

		subClassAxiom = dataFactory.getOWLSubClassOfAxiom(owlTaskClass, owlNodeClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, subClassAxiom));

		subClassAxiom = dataFactory.getOWLSubClassOfAxiom(owlEndClass, owlNodeClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, subClassAxiom));

		subClassAxiom = dataFactory.getOWLSubClassOfAxiom(owlJoinClass, owlNodeClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, subClassAxiom));
		
		OWLDisjointClassesAxiom disjointAxiom = dataFactory.getOWLDisjointClassesAxiom(owlTaskClass, owlStartClass, owlJoinClass, owlEndClass);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, disjointAxiom));
		
		//Declare basic individuals
		OWLIndividual start0 = dataFactory.getOWLNamedIndividual("#" + "start0", prefixManager);
		OWLClassAssertionAxiom classAssertionAxiom = dataFactory.getOWLClassAssertionAxiom(owlStartClass, start0);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, classAssertionAxiom));
		
		OWLIndividual end0 = dataFactory.getOWLNamedIndividual("#" + "end0", prefixManager);
		classAssertionAxiom = dataFactory.getOWLClassAssertionAxiom(owlEndClass, end0);		
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, classAssertionAxiom));
		
		// Declare basic diagram properties and its subproperties
		
		// follwedBy properties
		OWLObjectProperty followedByTranProperty = dataFactory.getOWLObjectProperty("#" + "followedByTran", prefixManager);
		System.out.println("relation: " + followedByTranProperty);	
		OWLTransitiveObjectPropertyAxiom transitiveAxiom = dataFactory.getOWLTransitiveObjectPropertyAxiom(followedByTranProperty);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, transitiveAxiom));
		
		OWLObjectProperty followedByProperty = dataFactory.getOWLObjectProperty("#" + "followedBy", prefixManager);
		System.out.println("relation: " + followedByProperty);
		OWLSubObjectPropertyOfAxiom followedByAxiom = dataFactory.getOWLSubObjectPropertyOfAxiom(followedByProperty, followedByTranProperty);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, followedByAxiom));
		
		OWLObjectProperty followedBy0Property = dataFactory.getOWLObjectProperty("#" + "followedBy0", prefixManager);
		System.out.println("relation: " + followedBy0Property);
		OWLSubObjectPropertyOfAxiom followedBy0Axiom = dataFactory.getOWLSubObjectPropertyOfAxiom(followedBy0Property, followedByProperty);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, followedBy0Axiom));
		
		// Contains properties
		OWLObjectProperty containsTranProperty = dataFactory.getOWLObjectProperty("#" + "ContainsTran", prefixManager);
		System.out.println("relation: " + containsTranProperty);	
		transitiveAxiom = dataFactory.getOWLTransitiveObjectPropertyAxiom(containsTranProperty);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, transitiveAxiom));
		
		OWLObjectProperty containsProperty = dataFactory.getOWLObjectProperty("#" + "Contains", prefixManager);
		System.out.println("relation: " + followedByProperty);
		OWLSubObjectPropertyOfAxiom containsAxiom = dataFactory.getOWLSubObjectPropertyOfAxiom(containsProperty, containsTranProperty);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, containsAxiom));

		// ContainedIn properties
		OWLObjectProperty containedTranProperty = dataFactory.getOWLObjectProperty("#" + "ContainedInTran", prefixManager);
		System.out.println("relation: " + containedTranProperty);	
		transitiveAxiom = dataFactory.getOWLTransitiveObjectPropertyAxiom(containedTranProperty);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, transitiveAxiom));
		
		OWLObjectProperty containedProperty = dataFactory.getOWLObjectProperty("#" + "ContainedIn", prefixManager);
		System.out.println("relation: " + containedProperty);
		OWLSubObjectPropertyOfAxiom containedInAxiom = dataFactory.getOWLSubObjectPropertyOfAxiom(containedProperty, containedTranProperty);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, containedInAxiom));
		
		// beginWith and endWith properties
		OWLObjectProperty beginsWithProperty = dataFactory.getOWLObjectProperty("#" + "beginsWith", prefixManager);
		System.out.println("relation: " + followedByProperty);
        OWLDeclarationAxiom beginsWithAxiom = dataFactory.getOWLDeclarationAxiom(beginsWithProperty);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, beginsWithAxiom));
		
		OWLObjectProperty beginsWith0Property = dataFactory.getOWLObjectProperty("#" + "beginsWith0", prefixManager);
		OWLSubObjectPropertyOfAxiom beginsWith0Axiom = dataFactory.getOWLSubObjectPropertyOfAxiom(beginsWith0Property, beginsWithProperty);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, beginsWith0Axiom));

		OWLClass owlSubProcessClass = dataFactory.getOWLClass("#" + "SubProcess", prefixManager);
		OWLObjectUnionOf classExpression = dataFactory.getOWLObjectUnionOf(owlSubProcessClass, owlProcessClass);
		
		OWLObjectProperty endsWithProperty = dataFactory.getOWLObjectProperty("#" + "endsWith", prefixManager);
		System.out.println("relation: " + followedByProperty);
        OWLDeclarationAxiom endsWithAxiom = dataFactory.getOWLDeclarationAxiom(endsWithProperty);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, endsWithAxiom));
		
		// Domain and range declaration
        Set<OWLAxiom> domainsAndRanges = new HashSet<OWLAxiom>();

        domainsAndRanges.add(dataFactory.getOWLObjectPropertyDomainAxiom(followedByTranProperty, owlNodeClass));
        domainsAndRanges.add(dataFactory.getOWLObjectPropertyRangeAxiom(followedByTranProperty, owlNodeClass));

        domainsAndRanges.add(dataFactory.getOWLObjectPropertyDomainAxiom(followedByProperty, owlNodeClass));
        domainsAndRanges.add(dataFactory.getOWLObjectPropertyRangeAxiom(followedByProperty, owlNodeClass));
        
        domainsAndRanges.add(dataFactory.getOWLObjectPropertyDomainAxiom(followedBy0Property, owlNodeClass));
        domainsAndRanges.add(dataFactory.getOWLObjectPropertyRangeAxiom(followedBy0Property, owlNodeClass));

        domainsAndRanges.add(dataFactory.getOWLObjectPropertyDomainAxiom(beginsWith0Property, classExpression));
		domainsAndRanges.add(dataFactory.getOWLObjectPropertyRangeAxiom(beginsWith0Property, owlNodeClass));

        domainsAndRanges.add(dataFactory.getOWLObjectPropertyDomainAxiom(beginsWithProperty, classExpression));
		domainsAndRanges.add(dataFactory.getOWLObjectPropertyRangeAxiom(beginsWithProperty, owlNodeClass));

        domainsAndRanges.add(dataFactory.getOWLObjectPropertyDomainAxiom(endsWithProperty, classExpression));
		domainsAndRanges.add(dataFactory.getOWLObjectPropertyRangeAxiom(endsWithProperty, owlNodeClass));

        domainsAndRanges.add(dataFactory.getOWLObjectPropertyDomainAxiom(containsProperty, classExpression));
		domainsAndRanges.add(dataFactory.getOWLObjectPropertyRangeAxiom(containsProperty, owlNodeClass));

        domainsAndRanges.add(dataFactory.getOWLObjectPropertyDomainAxiom(containsTranProperty, classExpression));
		domainsAndRanges.add(dataFactory.getOWLObjectPropertyRangeAxiom(containsTranProperty, owlNodeClass));

        domainsAndRanges.add(dataFactory.getOWLObjectPropertyDomainAxiom(containedProperty, classExpression));
		domainsAndRanges.add(dataFactory.getOWLObjectPropertyRangeAxiom(containedProperty, owlNodeClass));

        domainsAndRanges.add(dataFactory.getOWLObjectPropertyDomainAxiom(containedTranProperty, classExpression));
		domainsAndRanges.add(dataFactory.getOWLObjectPropertyRangeAxiom(containedTranProperty, owlNodeClass));

        // Generate data properties
		OWLDataProperty pairsWithProperty = dataFactory.getOWLDataProperty("#" + "pairsWith", prefixManager);
		System.out.println("relation: " + pairsWithProperty);
        OWLDeclarationAxiom pairsWithAxiom = dataFactory.getOWLDeclarationAxiom(pairsWithProperty);
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, pairsWithAxiom));
        
		OWLDatatype string = dataFactory.getOWLDatatype("xsd:string", prefixManager);
		
		classExpression = dataFactory.getOWLObjectUnionOf(owlSubProcessClass, owlTaskClass);
		domainsAndRanges.add(dataFactory.getOWLDataPropertyDomainAxiom(pairsWithProperty, classExpression));
        domainsAndRanges.add(dataFactory.getOWLDataPropertyRangeAxiom(pairsWithProperty, string));
        
        // Apply domains and range of all the properties
        owlOntologyManager.addAxioms(currentOntology, domainsAndRanges);
		
        // General class axioms
		OWLClassExpression followedByExactly1Node = dataFactory.getOWLObjectExactCardinality(1, followedByProperty, owlNodeClass);
		OWLObjectIntersectionOf generalAxiom = dataFactory.getOWLObjectIntersectionOf(owlEndClass, followedByExactly1Node);
		subClassAxiom = dataFactory.getOWLSubClassOfAxiom(generalAxiom, dataFactory.getOWLNothing());
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, subClassAxiom));
		OWLClassExpression followedByExactly1Start = dataFactory.getOWLObjectExactCardinality(1, followedByProperty, owlStartClass);		
		generalAxiom = dataFactory.getOWLObjectIntersectionOf(owlNodeClass, followedByExactly1Start);
		subClassAxiom = dataFactory.getOWLSubClassOfAxiom(generalAxiom, dataFactory.getOWLNothing());
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, subClassAxiom));
		
		// Declare the SWRL rules
		IRI xIRI = IRI.create(prefixManager.getDefaultPrefix() + "#x");
		IRI yIRI = IRI.create(prefixManager.getDefaultPrefix() + "#y");
		IRI zIRI = IRI.create(prefixManager.getDefaultPrefix() + "#z");
		SWRLIArgument x = dataFactory.getSWRLVariable(xIRI);
		SWRLIArgument y = dataFactory.getSWRLVariable(yIRI);
		SWRLIArgument z = dataFactory.getSWRLVariable(zIRI);
		
		SWRLObjectPropertyAtom beginsWithAtom = dataFactory.getSWRLObjectPropertyAtom(beginsWithProperty, y, z);
		SWRLObjectPropertyAtom followedByAtom1 = dataFactory.getSWRLObjectPropertyAtom(followedByProperty, x, y);
		SWRLClassAtom subProcessAtom = dataFactory.getSWRLClassAtom(owlSubProcessClass, y);
		SWRLClassAtom nodezAtom = dataFactory.getSWRLClassAtom(owlNodeClass, z);
		SWRLClassAtom nodexAtom = dataFactory.getSWRLClassAtom(owlNodeClass, x);
		SWRLObjectPropertyAtom followedByAtom2 = dataFactory.getSWRLObjectPropertyAtom(followedByProperty, x, z);
		Set<SWRLAtom> body = new HashSet<>();
		body.add(beginsWithAtom);
		body.add(followedByAtom1);
		body.add(subProcessAtom);
		body.add(nodezAtom);
		body.add(nodexAtom);
		Set<SWRLAtom> head = new HashSet<>();
		head.add(followedByAtom2);
		
		SWRLRule rule = dataFactory.getSWRLRule(body, head);
		
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, rule));
		
		body.clear();
		head.clear();
		
		SWRLObjectPropertyAtom endsWithAtom = dataFactory.getSWRLObjectPropertyAtom(endsWithProperty, y, z);
		followedByAtom1 = dataFactory.getSWRLObjectPropertyAtom(followedByProperty, y, x);
		subProcessAtom = dataFactory.getSWRLClassAtom(owlSubProcessClass, y);
		nodezAtom = dataFactory.getSWRLClassAtom(owlNodeClass, z);
		nodexAtom = dataFactory.getSWRLClassAtom(owlNodeClass, x);
		followedByAtom2 = dataFactory.getSWRLObjectPropertyAtom(followedByProperty, z, x);
		body.add(endsWithAtom);
		body.add(followedByAtom1);
		body.add(subProcessAtom);
		body.add(nodezAtom);
		body.add(nodexAtom);
		head.add(followedByAtom2);
		
		rule = dataFactory.getSWRLRule(body, head);
		
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, rule));
		
		body.clear();
		head.clear();
		
		SWRLObjectPropertyAtom containsAtom = dataFactory.getSWRLObjectPropertyAtom(containsProperty, x, y);
		SWRLObjectPropertyAtom containedAtom = dataFactory.getSWRLObjectPropertyAtom(containedProperty, y, x);
		
		body.add(containsAtom);
		head.add(containedAtom);

		rule = dataFactory.getSWRLRule(body, head);
		
		owlOntologyManager.applyChange(new AddAxiom(currentOntology, rule));
	}

	public OWLOntology owlFileGenerator(String proyectPath, String projectname)
			throws OWLOntologyCreationException, IOException, OWLOntologyStorageException {
		
		this.projectname = projectname.substring(0, projectname.lastIndexOf("."));
		this.proyectPath = proyectPath;
		
		// Create a new empty Owl file in appropriate directory
		this.projectname = this.projectname.replaceAll("(\\r|\\n|\\r\\n)+", "");
		this.projectname = this.projectname.replaceAll("[(]", "");
		this.projectname = this.projectname.replaceAll("[)]", "");
		this.projectname = this.projectname.replace(" ", "");
		this.projectname = this.projectname.replaceAll(",", "_");
		
		File file = new File(this.projectname + ".owl");
		///////////////////////////
		boolean fileCreated = file.createNewFile();
		System.out.println("fileCreated: " + fileCreated);
		//////////////////////////

		// Get IRI from new filepath
		IRI iriNewOntology = IRI.create(file);
		/////////////
		System.out.println("iriNewOntology: " + iriNewOntology);
		/////////////

		// Initialize owl ontology manager and owl data factory
		OWLDataFactory dataFactory = OWLManager.getOWLDataFactory();
		OWLOntologyManager owlOntologyManager = OWLManager.createOWLOntologyManager();

		// Create new ontology
		OWLOntology currentOntology = owlOntologyManager.createOntology(iriNewOntology);
		////////////////
		System.out.println("currentOntology: " + currentOntology);
		///////////////
		PrefixManager prefixManager = new DefaultPrefixManager(iriNewOntology.toString());

		generateBaseDiagramOntology(dataFactory, prefixManager, owlOntologyManager, currentOntology);

		extractOntologyFromDiagram(dataFactory, prefixManager, owlOntologyManager, currentOntology);
		
		owlOntologyManager.saveOntology(currentOntology);
		
		return currentOntology;

	}
}
