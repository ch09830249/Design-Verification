// apb_defines.svh
`ifndef APB_DEFINES_SVH
`define APB_DEFINES_SVH

// 定義資料與位址位寬
`define APB_DATA_WIDTH  32
`define APB_ADDR_WIDTH  10
`define APB_WAIT_CYCLES 8

// 你也可以順便定義一些常用的狀態
`define APB_IDLE   2'b00
`define APB_SETUP  2'b01
`define APB_ACCESS 2'b10

`endif