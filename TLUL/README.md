# TLUL
* TileLink 無緩存羽量級（TL-UL）是最簡單的 TileLink 協定，可用於連接低性能的外設以減小總線的面積消耗。TLUL 支援 2 種存取操作：
  * **讀（Get）操作**：從底層記憶體中讀取一定量的數據。
  * **寫（Put）操作**：向底層記憶體中寫入一定數目的數據，寫操作支援基於位元組掩碼的部分寫功能。
在 TL-UL 中，每條消息都必須放在一拍中，不支援 burst 操作，TL-UL 一共定義了與存取訪問操作相關的 **3 種請求消息**和 **2 種回應消息**類型，下表列舉了這些消息。
![image](https://github.com/user-attachments/assets/19f9b87f-fb1f-4179-ae6b-0aebef8c5b02)
# Wave form
![image](https://github.com/user-attachments/assets/3965eb1a-3cdb-4b4e-80b7-7f4ee369b01b)
Waveform containing Get and Put operations. 
* PutFullData writes 0xabcd;
* Get reads 0xabcd; PutFullData writes 0x0000;
* PutPartialData writes part of 0xffff;
* Get reads 0x00ff.
# Message Flow
* **Get message flow**: A master sends a Get to a slave. Having read the required data, the slave responds to the master with an AccessAckData.
![image](https://github.com/user-attachments/assets/663959d3-486b-4fcb-b8a8-f58f44324856)
* **Put message flow**: A master sends an PutPartialData or PutFullData to a slave. After writing the included data, the slave responds to the master with a
AccessAck.
![image](https://github.com/user-attachments/assets/4852218c-adb7-4898-923c-c6ed53e6015d)
* **Message flow across multiple hierarchical agents** to perform a memory access that reads a block of data. The Hierarchical Agent forwards the Get to the outer Slave Agent and then also forwards the response AccessAckData to the Master Agent.
![image](https://github.com/user-attachments/assets/e2520e61-5ea2-4794-afde-d95d8d775624)
# Signals
## Get
* a_param is currently reserved for future performance hints and must be 0.
* a_size indicates the total amount of data the requesting agent wishes to read, **in terms of log2(bytes)**. a size represents the size of the resulting AccessAckData response message, not this particular Get message. In TL-UL, a size cannot be larger than the width of the physical data bus.
![image](https://github.com/user-attachments/assets/54f8176d-1ed1-4187-8a7f-88cad54eb4e6)
## PutFullData
![image](https://github.com/user-attachments/assets/10711927-d18d-4e03-9799-22da744e4c3c)
## PutPartialData
![image](https://github.com/user-attachments/assets/21d3e37b-c1e0-4d9d-a1ff-5fe9c94a6920)
## AccessAck
![image](https://github.com/user-attachments/assets/0e6ebdc1-c9d1-4988-8ed0-5c0ab871af88)
## AccessAckData
![image](https://github.com/user-attachments/assets/f5dd41db-2dfd-43e9-8e5b-3d51994b75d5)

# Reference
TileLink筆記（三）：TL-UL: https://zhuanlan.zhihu.com/p/575707311
