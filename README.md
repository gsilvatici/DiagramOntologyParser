
# DiagramOntologyParser

This program takes a Camunda BPM process diagram and translates it to a ontology.

## Usage

Run the .jar file, the program will display a button to select a camunda bpm file to translate ta a ontology,
the translated ontologies will be displayed on the "generated ontology" section in the middle of the screen.
It will generate a "output.owl" file which contains all the process model translated and merged to a owl file 
(a KB with all the process models).
By clicking on the buttons with the process models it will delete the process on the final generated ontology.

## Considerations

The goal of the software is to generate ontologies (owl files) from bpm files, so for reasoning and querying the generated ontologies
it must make use of utilities like Protégé.

## Author

Gabriel Silvatici.
