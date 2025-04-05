# Base Classes
* The basic building blocks for any verification environment are the **components (drivers, sequencers, monitors ...)**
* The **transactions (class objects that contain actual data)** they use to communicate.
* From the UVM hierarchy, we can see that most of the classes in UVM are derived from a set of core classes that are described below.
![image](https://github.com/user-attachments/assets/331cc465-4ca5-4ca9-8c23-73f3405535a2)
## uvm_void
```
virtual class uvm_void;
endclass
```
* This **doesn't have any purpose**, but serves as the base class for all UVM classes.
* It is an **abstract class** with **no data members or functions**.
* It allows for generic containers of objects to be created, **similar to a void pointer** in the C programming language. 像是一個 void pointer 可以指向任何型態的物件
* User classes derived directly from uvm_void **inherit none of the UVM functionality**, but such classes may be placed in uvm_void typed containers along with other UVM objects.
## uvm_object
* This is a **virtual base class for all components and transactions** in the UVM testbench. It's primary role is to define a set of methods for common operations like print, copy, compare and record.
```
virtual class uvm_object extends uvm_void;

	extern function void print (uvm_printer printer=null);
 	extern function void copy (uvm_object rhs, uvm_copier copier=null);
  extern function bit  compare (uvm_object rhs, uvm_comparer comparer=null);
 	extern function void record (uvm_recorder recorder=null);
	...

endclass
```
## uvm_report_object
* Provides an interface to the UVM reporting facility.
  * **All messages, warnings, errors issued by components go via this interface.**
  * There's an internal instance of uvm_report_handler which stores the reporting configuration on the basis of which the handler makes decisions on whether the message should be printed or not. Then it's passed to a central uvm_report_server which does the actual formatting and production of messages.
```
// A report has 'severity', 'id_string', 'text_message', and 'verbosity_level'
`uvm_info ("STAT", "Status register updated", UVM_HIGH")

// severity  		: uvm_info
// id_string 		: "STAT"
// text_message 	: "Status register updated"
// verbosity_level 	: UVM_HIGH
```
* The message is ignored if the verbosity level is greater than the configured maximum verbosity level.
  * For example, if the maximum verbosity level is set to UVM_MEDIUM, then all INFO statements with verbosity greater than MEDIUM are ignored. This is useful for debug purposes where the message level can be set to UVM_HIGH for all debug related messages, while the maximum verbosity level is set to UVM_MEDIUM. This allows the ability to switch between different output levels without recompiling the testbench.
