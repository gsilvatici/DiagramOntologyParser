package ontologybuilder;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AddAxiom;
import org.semanticweb.owlapi.model.AddImport;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDeclarationAxiom;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLImportsDeclaration;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.util.OWLEntityRenamer;
import org.semanticweb.owlapi.util.OWLOntologyMerger;

public class OntologyMerger {
	
	private ArrayList<OWLOntology> ontologies;
    private OWLOntologyManager man;
    private String fileName;
    private ArrayList<String> entitiesNames;
    private ArrayList<String> commonClasses;
    private ArrayList<OWLClass> conceptClasses;
    private OWLOntology mergedOntology;
	private OWLDataFactory dataFactory;
    
    public OntologyMerger(ArrayList<OWLOntology> ontologies, String filename) throws OWLOntologyStorageException, IOException{

		// Initialize owl ontology manager and owl data factory
		this.man = OWLManager.createOWLOntologyManager();		
        this.ontologies = ontologies;
        this.fileName = filename;
        this.entitiesNames = new ArrayList<>();
        this.commonClasses = new ArrayList<>();
        this.conceptClasses = new ArrayList<>();
        this.dataFactory = OWLManager.getOWLDataFactory();
        //call the merging process
        mergeOntologies();
    }

    private void mergeOntologies() throws OWLOntologyStorageException, IOException{
		File file = new File(this.fileName + ".owl");
		///////////////////////////
		boolean fileCreated = file.createNewFile();
		System.out.println("fileCreated: " + fileCreated);
		//////////////////////////
    	
    	IRI mergedOntologyIRI = IRI.create(file);
    	
    	    //Using HashSet to avoid duplicated entries
    	    Set<OWLAxiom> axioms = new HashSet<OWLAxiom>();
    	    Set<OWLImportsDeclaration> imports = new HashSet<OWLImportsDeclaration>();
    	    try{    
    	        for (OWLOntology ontology : ontologies){
//    	            man.loadOntologyFromOntologyDocument(ontology.getFile());
    	            axioms.addAll(ontology.getAxioms());
    	            imports.addAll(ontology.getImportsDeclarations());
//    	            man.removeOntology(ontology.getOntology()); 
    	        } 
    	        mergedOntology = man.createOntology(mergedOntologyIRI);
    	        man.addAxioms(mergedOntology, axioms);
    	    } catch (OWLOntologyCreationException e) {
    	        e.printStackTrace();
    	    } 
    	    //Adding the import declarations
    	    for(OWLImportsDeclaration decl : imports){
    	        man.applyChange(new AddImport(mergedOntology, decl));
    	    }
    	    //rename individuals names to use the merged ontology's IRI
    	    renameIRIs(mergedOntologyIRI);
    		man.saveOntology(mergedOntology);
    	}

    	  private void renameIRIs(IRI newIRI){
    	        OWLEntityRenamer renamer = new OWLEntityRenamer(man, man.getOntologies());

    	        for (OWLOntology ontology : ontologies){
    	            for (OWLEntity entity : ontology.getSignature()){
    	            	
    	                //replace the individual's old IRI with the new one E.g: http://ontologyOld#name becomes newIRI#name
    	            	String currentIRI = entity.getIRI().toString().replaceFirst("[^*]+(?=#|;)", newIRI.toString());
    	            	
    	            	String[] strings = currentIRI.toString().split("#");
    	            	ArrayList<String> aux = new ArrayList<>();
    	            	aux.add(strings[0] + "#Node");
    	            	aux.add(strings[0] + "#SubProcess");
    	            	aux.add(strings[0] + "#ConceptActivity");
    	            	aux.add(strings[0] + "#End");
    	            	aux.add(strings[0] + "#Start");
    	            	aux.add(strings[0] + "#Task");
    	            	aux.add(strings[0] + "#Join");
    	            	aux.add(strings[0] + "#Nothing");

    	            	
    	            	if (entity.isOWLClass() && !aux.contains(currentIRI)) {

        	            	if (entitiesNames.contains(currentIRI)) {
        	            		
        	            		int index = entitiesNames.indexOf(currentIRI);
        	            		String classIRI = currentIRI;
        	            		OWLClass owlConceptActClass = dataFactory.getOWLClass(IRI.create(currentIRI));
        	            		        	            		
        	            		if (commonClasses.contains(currentIRI)) {
            	            		while (entitiesNames.contains(currentIRI)) {
                	            		currentIRI = currentIRI + "*";
            	            		}        	
            	            		entitiesNames.add(currentIRI);
        	            	
	    	    	                IRI entityName = IRI.create(currentIRI);
	    	    	                man.applyChanges(renamer.changeIRI(entity.getIRI(), entityName));

	        	            		Set<OWLAxiom> axiomsToRemove = new HashSet<>();
	        	            		OWLClass conceptActivity = dataFactory.getOWLClass(IRI.create(currentIRI));
	        	            		for (OWLAxiom each: conceptActivity.getReferencingAxioms(mergedOntology)) {
	        	            			if (each.isOfType(AxiomType.SUBCLASS_OF)) {
	        	            		        axiomsToRemove.add(each);
	        	            			}
	        	            		}	        	            		
	        	            		OWLSubClassOfAxiom subClassAxiom = dataFactory.getOWLSubClassOfAxiom(conceptActivity, owlConceptActClass);
	        	            		man.applyChange(new AddAxiom(mergedOntology, subClassAxiom));

	        	            		man.removeAxioms(mergedOntology, axiomsToRemove);
	        	            		
        	            		} else {             	            		
        	            			commonClasses.add(currentIRI);
        	            			currentIRI = currentIRI + "*";        	            			
	    	    	                IRI entityName = IRI.create(currentIRI);
	    	    	                man.applyChanges(renamer.changeIRI(entity.getIRI(), entityName));
	    	    	                entitiesNames.add(currentIRI);
	    	    	                
	    	    	                currentIRI = currentIRI + "*";	    	    	                	    	    	                
        	            			OWLClass superClass = conceptClasses.get(index);
        	            			entityName = IRI.create(currentIRI);
	    	    	                man.applyChanges(renamer.changeIRI(IRI.create(classIRI), entityName));        	       
	    	    	                entitiesNames.add(currentIRI);
	    	    	                
	    	    	                OWLClass conceptActivity = dataFactory.getOWLClass(IRI.create(strings[0] + "#ConceptActivity"));
	    	    	                OWLSubClassOfAxiom subClassAxiom = dataFactory.getOWLSubClassOfAxiom(owlConceptActClass, conceptActivity);
	        	            		man.applyChange(new AddAxiom(mergedOntology, subClassAxiom));

	        	            		Set<OWLAxiom> axiomsToRemove = new HashSet<>();
	        	            		conceptActivity = dataFactory.getOWLClass(IRI.create(classIRI + "*"));
	        	            		for (OWLAxiom each: conceptActivity.getReferencingAxioms(mergedOntology)) {
	        	            			if (each.isOfType(AxiomType.SUBCLASS_OF)) {
	        	            		        axiomsToRemove.add(each);
	        	            			}
	        	            		}	        	            		
	    	    	                subClassAxiom = dataFactory.getOWLSubClassOfAxiom(conceptActivity, owlConceptActClass);
	        	            		man.applyChange(new AddAxiom(mergedOntology, subClassAxiom));

	        	            		conceptActivity = dataFactory.getOWLClass(IRI.create(classIRI + "**"));
	        	            		for (OWLAxiom each: conceptActivity.getReferencingAxioms(mergedOntology)) {
	        	            			if (each.isOfType(AxiomType.SUBCLASS_OF)) {
	        	            		        axiomsToRemove.add(each);
	        	            			}
	        	            		}
	    	    	                subClassAxiom = dataFactory.getOWLSubClassOfAxiom(conceptActivity, owlConceptActClass);
	        	            		man.applyChange(new AddAxiom(mergedOntology, subClassAxiom));
	        	            		
	        	            		man.removeAxioms(mergedOntology, axiomsToRemove);
        	            		}
        	            		
        	            		
        	            	} else {
    	    	                IRI entityName = IRI.create(currentIRI);
    	    	                man.applyChanges(renamer.changeIRI(entity.getIRI(), entityName));
        	            		conceptClasses.add((OWLClass)entity);
        	            		if (!currentIRI.endsWith("Process")) {
        	            			entitiesNames.add(currentIRI);
        	            		}
        	            	}
    	            	} else {    	              	            	    	  
	    	                IRI entityName = IRI.create(currentIRI);
	    	                man.applyChanges(renamer.changeIRI(entity.getIRI(), entityName));
    	            	}
    	            	
    	            }
    	        }   
    	    }
}
