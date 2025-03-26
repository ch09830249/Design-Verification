# UVM Sequencer
![image](https://github.com/user-attachments/assets/a9426e57-1af6-42f7-adb4-68d1012762b9)
* Sequencer 產生 data transactions 並且傳給 Driver
* 建議直接 extend uvm_sequencer 因為該 class 已包含所有與 Driver 溝通的功能
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
