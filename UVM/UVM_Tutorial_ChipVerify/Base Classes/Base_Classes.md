# Base Classes
The **basic building blocks** for any verification environment are the **components** (drivers, sequencers, monitors ...) and the **transactions (class objects that contain actual data)** they **use to communicate**. From the UVM hierarchy, we can see that most of the classes in UVM are derived from a set of core classes that are described below.
![image](https://github.com/user-attachments/assets/8e9fe0ac-21e1-4a42-a39d-1a1bf63ae6cc)
## uvm_void
```
virtual class uvm_void;
endclass
```
* Doesn't have any purpose, but serves as the base class for all UVM classes.
* An **abstract class with no data members or functions**
* It allows for generic containers of objects to be created, **similar to a void pointer in the C programming language**. User classes derived directly from uvm_void inherit none of the UVM functionality, but such classes may **be placed in uvm_void typed containers** along with other UVM objects.  
(uvm_void 的 handle 可以去接住所有 uvm 的物件, 類似 C 語言 void pointer 可以指向任何型態的資料型態)
## uvm_object
```
virtual class uvm_object extends uvm_void;

	extern function void print (uvm_printer printer=null);
 	extern function void copy (uvm_object rhs, uvm_copier copier=null);
  extern function bit  compare (uvm_object rhs, uvm_comparer comparer=null);
 	extern function void record (uvm_recorder recorder=null);
	...

endclass
```
* This is a virtual base class for **all components and transactions** in the UVM testbench.
* It's primary role is to define a set of methods for common operations like **print, copy, compare and record**.
## uvm_report_object
```
// A report has 'severity', 'id_string', 'text_message', and 'verbosity_level'
`uvm_info ("STAT", "Status register updated", UVM_HIGH")

// severity  		: uvm_info
// id_string 		: "STAT"
// text_message 	: "Status register updated"
// verbosity_level 	: UVM_HIGH
```
* Provides an interface to the **UVM reporting facility**.  
  (在這一層有一些印 log 相關介面)
  * **All messages, warnings, errors issued** by components go via this interface.
  * An internal instance of uvm_report_handler
    * **Store the reporting configuration**
    * **Make decisions on whether the message should be printed or not**.
    * Pass to a central uvm_report_server which does the **actual formatting and production of messages**.
* The message is ignored if the **verbosity level is greater than the configured maximum verbosity level**.
## uvm_component
* All major verification components like agents and drivers are derived from uvm_component. It has the following interfaces:
  * **Hierarchy**: Defines methods for searching and traversing the component hierarchy like env0.pci0.master1.drv  
    (Component 有結構樹的概念, 所以在實例化 component 時, 會需要指定 parent 以便結構樹的建立, 方便未來 method 和 component 的搜尋和走訪)
  * **Phasing**: Defines a phasing system that all components can follow eg : **build, connect, run**, etc  
    (Compnent 也有 Phases 機制, 將測試的工作模組化, developer 只需對 virtua method 去 Override 就可以方便的開發以及維護)
  * **Reporting** : Defines an interface to the Report Handler, and all messages, warnings and errors are processed through this interface (derived from uvm_report_object)
  * **Recording** : Defines methods to record transactions produced/consumed by component to a transaction database.
  * **Factory** : Defines an interface to the uvm_factory (used to create new components/objects based on instance/type)  
    (Component 有 Factory 機制, 不只方便 Component 實例化, 同時也方便為 component 的置換 (透過 Override 機制))
## uvm_transaction
  * This is an extension of uvm_object and includes a timing and recording interface.
  * Note that **simple transactions can be derived from uvm_transaction**, but **sequence-enabled transactions must be derived from uvm_sequence_item**.
## uvm_root
  * An **implicit top-level UVM component** that is **automatically created when the simulation is run**
  * Users can access via the global uvm_pkg:: variable, uvm_top, which has the following properties:
    * **Any component whose parent is set to null becomes a child of uvm_top**
    * It manages the phasing for all components
    * It is used to **search for components based on their hierarchical name**  
      (在實例化 component 時, 第一個參數就是指定該 component 名稱)
    * It is used to globally configure report verbosity
    * UVM's reporting mechanism is accessible from anywhere outside uvm_component such as in modules and sequences
It's worthwhile to note that uvm_top checks for errors during end_of_elaboration phase and issues a UVM_FATAL error to stop simulation from starting.
