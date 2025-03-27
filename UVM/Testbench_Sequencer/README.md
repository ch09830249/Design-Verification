# UVM Sequencer
![image](https://github.com/user-attachments/assets/a9426e57-1af6-42f7-adb4-68d1012762b9)
* A sequencer **generates data transactions** as class objects and **sends it to the Driver** for execution.
* It is recommended to extend uvm_sequencer base class since it contains all of the functionality required to allow a sequence to communicate with a driver.
* The base class is parameterized by the request and response item types that can be handled by the sequencer.
# Class Hierarchy
![image](https://github.com/user-attachments/assets/f6ac68e3-ad40-4c90-b210-2deb3dc7f01c)
# 用法
# Custom Sequencer
* 不太需要 customized 直接繼承
```
class my_sequencer extends uvm_sequencer;
	`uvm_component_utils (my_sequencer)
	function new (string name="m_sequencer", uvm_component parent);
		super.new (name, parent);
	endfunction

endclass
```
