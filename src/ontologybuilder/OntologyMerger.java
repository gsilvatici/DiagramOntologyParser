package ontologybuilder;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AddImport;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLImportsDeclaration;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.util.OWLEntityRenamer;
import org.semanticweb.owlapi.util.OWLOntologyMerger;

public class OntologyMerger {
	
	private ArrayList<OWLOntology> ontologies;
    private OWLOntologyManager man;
    private String fileName;
    private OWLOntology mergedOntology;

    public OntologyMerger(ArrayList<OWLOntology> ontologies, String filename) throws OWLOntologyStorageException, IOException{

		// Initialize owl ontology manager and owl data factory
		this.man = OWLManager.createOWLOntologyManager();		
        this.ontologies = ontologies;
        this.fileName = "prueba";
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
    	        for(OWLOntology ontology : ontologies){
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

    	  private void renameIRIs (IRI newIRI){
    	        OWLEntityRenamer renamer = new OWLEntityRenamer(man, man.getOntologies());

    	        for(OWLOntology ontology : ontologies){
    	            for ( OWLEntity individual : ontology.getSignature()){
    	                //replace the individual's old IRI with the new one E.g: http://ontologyOld#name becomes newIRI#name
    	                IRI individualName = IRI.create(individual.getIRI().toString().replaceFirst("[^*]+(?=#|;)", newIRI.toString()));
    	                man.applyChanges(renamer.changeIRI(individual.getIRI(), individualName));
    	            }
    	        }   
    	    }
}
