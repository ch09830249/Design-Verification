# Resource Database
* A resource is a parameterized container that holds arbitrary data. Resources can be used to **configure components, supply data to sequences, or enable sharing of information across disparate parts of the testbench**. They are stored using **scoping information** so their visibility can be **constrained to certain parts of the testbench**. You can put any data type into the resource database, and have another component retrieve it later at some point in simulation, which is a very convenient feature to have.
* 有點像 shared memory, 但是有 scope 資訊, 只有部分的 component 看的到或取用  
![image](https://github.com/user-attachments/assets/15d026cb-6e4d-450c-a3ff-dd99b549e3e7)  

**Name**: The "name" by which this resource is stored in the database. The same "name" has to be supplied to retrieve it later. (看作是該 resource 的一個 label)  
**Value**: The value that should be stored in the database for the given "name". (該 resource)  
**Scope**: A regular expression that specifies the scope over which this resource is visible to other components in the testbench. (限定那些 components 可以看到該 resource)  
**Type**: The data type of the object that this resource contains. It can be a string, int, virtual interface, class object, or any other valid SystemVerilog data-type. (該 resource 的 data type)  
![image](https://github.com/user-attachments/assets/5233eebf-7f4f-42a3-94c6-364f64365d56)

The global resource database has both a **name table** and a **type table** into which each resource is entered. So, **the same resource can be retrieved later by name or type**. Multiple resources with the same name/type are stored in a queue and hence those which were pushed in earlier have more precedence over those placed later. In the image above, if a request to retrieve an item of type string is made, the queue is traversed from front to back, and first ocurrence of an object of string type will be returned. Now, consider the case where items 2(red) and 3(blue) in the queue have the same scope, and a get_by_type() method is called for that particular scope. Then item 2(red) will be returned since that sits earlier in the queue.

![image](https://github.com/user-attachments/assets/a47baf99-06a9-4886-9817-06caeeeba1e5)

Resources are added to the pool by calling set, and they are retrieved from the pool by get_by_name() or get_by_type(). Another interesting feature is that the resource pool/database contains a history of gets. Whenever a component uses the above methods to retrieve an object, it will be recorded (both successful and failed gets), which can be dumped at the end of simulation. This can be a very good tool during debug.

# Config DB
## set() (在 Config DB 中, 創建新的或更新既有的資料)
```
static function void set (  uvm_component cntxt,
                            string        inst_name,
                            string        field_name,
                            T             value);
```
* Create a new or update an existing configuration setting for field_name in inst_name from cntxt
* Full scope of the set being **{cntxt, ".", inst_name}** (這裡確定了該 resource 的可視範圍)
  * If cntxt is null, then the complete scope of getting the information will be provided by inst_name.
* In the last example the cntxt is **this**, and will be substituted by the path to the current component which in this case is "uvm_test_top.m_env.m_apb_agent". As explained above the full scope becomes "uvm_test_top.m_env.m_apb_agent.*
```
// Set virtual interface handle under name "apb_vif" available to all components below uvm_test_top, indicated by the *
uvm_config_db #(virtual apb_if) :: set (null, "uvm_test_top.*", "apb_vif", apb_if);

// Set an int variable to turn on coverage collection for all components under m_apb_agent
uvm_config_db #(int) :: set (null, "uvm_test_top.m_env.m_apb_agent.*", "cov_enable", 1);

// Consider you are in agent's build_phase then you may achieve the same effect by
uvm_config_db #(int) :: set (this, "*", "cov_enable", 1);
```
![image](https://github.com/user-attachments/assets/8fc3f380-0498-4ac5-a936-dffdbfa5807a)
## get()
```
static function bit get (      uvm_component  cntxt,
                               string         inst_name,
                               string         field_name,
                               inout   T      value);
```
* Get the value of variable given in field_name from the configuration database
* If you had set a variable by **field_name m_cfg** at **scope "uvm_test_top.m_env.m_func_cov"**, then you have to give the same scope that is true for the expression.
```
// Get virtual interface handle under name "apb_vif" into local virtual interface handle at m_env level
uvm_config_db #(virtual apb_if) :: get (this, "*", "apb_vif", apb_if);

// Get int variable fails because no int variable found in given scope
uvm_config_db #(int) :: get (null, "uvm_test_top", "cov_enable", cov_var);
```
## exists()
```
static function bit exists (  uvm_component cntxt,
                              string        inst_name,
                              string        field_name,
                              bit           spell_chk);
```
* The spell_chk arg can be set to 1 to turn spell checking on if it is expected that the field should exist in the database.
```
// Check if interface handle exists at the given scope
if (! uvm_config_db #(virtual apb_if) :: exists (this, "*", "apb_vif"))
	`uvm_error ("VIF", "Could not find an interface handle", UVM_MEDIUM)
```
## wait_modified()
```
static task wait_modified ( uvm_component cntxt,
                            string        inst_name,
                            string        field_name);
```
* Use of this task will block execution of statements following this until the configuration setting named in field_name specified at scope {cntxt.inst_name} is changed.
```
class my_agent extends uvm_agent;

	virtual task run_phase (uvm_phase phase);
		...
		// Waits until loopCount variable gets a new value
		uvm_config_db #(int) :: wait_modified (this, "", "loopCount");
	endtask
endclass

class my_env extends uvm_env;

	my_agent m_apb_agent;

	virtual task main_phase (uvm_phase phase);
		...
		// Update loopCount variable in database
		for (int i = 0; i < N; i++) begin
			...
			uvm_config_db #(int) :: set (this, "m_apb_agent", "loopCount", i);
		end
	endtask
endclass
```
