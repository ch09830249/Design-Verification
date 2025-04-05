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
