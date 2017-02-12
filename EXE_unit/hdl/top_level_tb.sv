// =======================================================================
//   Department of Electrical and Computer Engineering
//   Portland State University
//
//   Course name:  ECE 510 - Pre-Silicon Validation
//   Term & Year:  Spring 2016
//   Project Team: Surendra Maddula, Bharath Reddy Godi.
//
//   Project:      Hardware implementation of PDP8 
//                 Instruction Set Architecture (ISA) level simulator
//
//   Filename:     top_level_tb.sv
//   Description:  Top level testbench module
//   Created by:   Surendra Maddula
//   Date:         May 23, 2016
//
//   Copyright:    Surendra Maddula, Bharath Reddy Godi
// =======================================================================
`timescale 1ns/1ps

import pdp8_pkg::*;

`include "pdp8_pkg.sv"

module top_level_tb ();

wire                   clk;
wire 									reset_n;
wire 									stall;
wire [`ADDR_WIDTH-1:0] PC_value;

wire 									exec_rd_req;
wire [`ADDR_WIDTH-1:0] exec_rd_addr;

wire                   exec_wr_req;
wire [`ADDR_WIDTH-1:0] exec_wr_addr;
wire [`DATA_WIDTH-1:0] exec_wr_data;
wire [`DATA_WIDTH-1:0] exec_rd_data;

wire [`ADDR_WIDTH-1:0] base_addr;
pdp_mem_opcode_s pdp_mem_opcode;
pdp_op7_opcode_s pdp_op7_opcode;



	memory_pdp_stub MEM(	.clk         		 (clk),
									.exec_rd_req     (exec_rd_req),
									.exec_rd_addr    (exec_rd_addr),
									.exec_rd_data    (exec_rd_data),
									.exec_wr_req     (exec_wr_req),
									.exec_wr_addr    (exec_wr_addr),
									.exec_wr_data    (exec_wr_data));
													


clkgen_driver #(
   .CLOCK_PERIOD(10)) clkgen_driver (
   .clk     (clk),
   .reset_n (reset_n));

instr_decode_stub DEC(	.clk             (clk),
									.reset_n         (reset_n),
									.stall           (stall),
									.PC_value        (PC_value),
									.base_addr       (base_addr),
									.pdp_mem_opcode  (pdp_mem_opcode),
									.pdp_op7_opcode  (pdp_op7_opcode));								

												

instr_exec EXE(	.clk          		(clk),
								.reset_n      		(reset_n),
								.base_addr        (base_addr),
								.pdp_mem_opcode   (pdp_mem_opcode),
								.pdp_op7_opcode   (pdp_op7_opcode),
								.stall      			(stall),
								.PC_value         (PC_value),
								.exec_wr_req      (exec_wr_req),
								.exec_wr_addr     (exec_wr_addr),
								.exec_wr_data     (exec_wr_data),
								.exec_rd_req			(exec_rd_req),
								.exec_rd_addr 		(exec_rd_addr),
								.exec_rd_data 		(exec_rd_data));	

	
exe_checker CHEK(    						.clk (clk),
								.reset_n(reset_n),
								.base_addr(base_addr),
								.pdp_mem_opcode(pdp_mem_opcode),
								.pdp_op7_opcode(pdp_op7_opcode),
								.stall(stall),
								.PC_value(PC_value),
								.exec_wr_req(exec_wr_req),
								.exec_wr_addr(exec_wr_addr),
								.exec_wr_data(exec_wr_data),
								.exec_rd_req(exec_rd_req),
								.exec_rd_addr(exec_rd_addr),
								.exec_rd_data(exec_rd_data) )					;
												

endmodule
