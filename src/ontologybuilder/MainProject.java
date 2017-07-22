

package ontologybuilder;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import javax.swing.*;

import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;



public class MainProject implements ActionListener{
    private JFrame mainWindow;
    private JPanel iconPanel;
    private JPanel areaPanel;
    private JButton select_file;
    JPanel input;
    Font font= new Font("Lucida Console", Font.PLAIN, 20);
    public void createMainWindow(){
        mainWindow = new JFrame("Process Diagram Querying");
        mainWindow.setExtendedState(JFrame.MAXIMIZED_BOTH);
        mainWindow.setSize(1000,730);
        mainWindow.setVisible(true);        
        //creation of a main icon panel
        iconPanel = new JPanel();
        iconPanel.setBackground(new Color(100, 138, 230));
        iconPanel.setPreferredSize(new Dimension(50,50));
        mainWindow.add(iconPanel,BorderLayout.NORTH);
        
        //creation of a work area panel
        Color color=new Color(230, 230, 230);
        areaPanel = new JPanel();
        areaPanel.setBackground(color);
//        areaPanel.setPreferredSize(new Dimension(600,600));
        mainWindow.add(areaPanel);
        
        //choose file button
        select_file = new JButton("Select BPMN Camunda file");
        select_file.setVisible(true);
        select_file.setEnabled(true);
        select_file.setBackground(new Color(175, 175, 175));
        iconPanel.add(select_file);

        select_file.addActionListener(this);
    }
    public void createActivity(){
        areaPanel.revalidate();
        areaPanel.removeAll();
        areaPanel.repaint();
        
        //creating a input panel
        input = new JPanel();
        input.setPreferredSize(new Dimension(200,400));
        input.setBackground(Color.LIGHT_GRAY);
        input.setVisible(true);
        areaPanel.add(input);

        //setting labels
        JLabel in_lb = new JLabel("Input");
        in_lb.setFont(font);
        in_lb.setBorder(BorderFactory.createEmptyBorder(8, 200, 10, 190));
        in_lb.setForeground(Color.WHITE);
        in_lb.setOpaque(true);
        in_lb.setBackground(Color.BLACK);
        input.add(in_lb);
        
    }
    public void createView() throws IOException{
        areaPanel.revalidate();
        areaPanel.removeAll();
        areaPanel.repaint();        
    }

    public static void main(String args[]){
        MainProject g1 = new MainProject();
        g1.createMainWindow();
        g1.createActivity();
    }

    @Override
    public void actionPerformed(ActionEvent ae) {

        if(ae.getSource() == select_file){
            JFileChooser chooser = new JFileChooser();

            chooser.setAcceptAllFileFilterUsed(false);
            chooser.setDialogTitle("Choose the Model File");
            chooser.setApproveButtonText("Select");

            chooser.showOpenDialog(null);

            String proyectPath = chooser.getSelectedFile().getAbsolutePath();
            String projectname = chooser.getSelectedFile().getName();
            System.out.println(proyectPath);
            System.out.println(projectname);
            
            //setting process names            
            JButton btn = new JButton(projectname);
            btn.setPreferredSize(new Dimension(200,40));
            btn.setBorder(BorderFactory.createLoweredSoftBevelBorder());
            btn.addActionListener(this);
            input.add(btn);
            
            btn.addActionListener(new ActionListener() {

                public void actionPerformed(ActionEvent e)
                {
                    //Execute when button is pressed
                	
                }
            });    
            
            input.revalidate();
            input.repaint();
            
            DiagramParserC dp = new DiagramParserC();
            try {
				dp.owlFileGenerator(proyectPath, projectname);
			} catch (OWLOntologyCreationException | OWLOntologyStorageException | IOException e) {
				System.out.println("System exception: unreachable file path");
			}
            
        }    

    }
}
