// =======================================================================
//   Department of Electrical and Computer Engineering
//   Portland State University
//
//   Course name:  ECE 510 - Pre-Silicon Validation
//   Term & Year:  Spring 2016
//   Instructor :  Tareque Ahmad
//   Project Team: Surendra Maddula, Bharath Reddy Godi.
//
//   Project:      Hardware implementation of PDP8 
//                 Instruction Set Architecture (ISA) level simulator
//
//   Filename:     memory_pdp.sv
//   Description:  TBD
//   Created by:   Bharath Reddy Godi
//   Date:         May 23, 2016
//
//   Copyright:    Surendra Maddula, Bharath Reddy Godi
// =======================================================================

`timescale 1ns/1ps

`include "pdp8_pkg.sv"
import pdp8_pkg::*;

module memory_pdp_stub
  (
   // Global input
   input clk,

   input                    exec_rd_req,
   input  [`ADDR_WIDTH-1:0] exec_rd_addr,
   output [`DATA_WIDTH-1:0] exec_rd_data,

   input                    exec_wr_req,
   input  [`ADDR_WIDTH-1:0] exec_wr_addr,
   input  [`DATA_WIDTH-1:0] exec_wr_data

   );

   reg [`ADDR_WIDTH-1:0] int_exec_rd_addr;
   reg [`DATA_WIDTH-1:0] int_exec_rd_data, ran1;


initial begin

   //array = '{`NOP,`HLT,`CLL,`CLA1,`CLA_CLL,`CLA2,`IAC,`RAL,`RTL,`RAR,`RTR,`CML,`CMA,`CIA,`OSR,`SKP,`SNL,`SZL,`SZA,`SNA,`SMA,`SPA};
   //int_exec_rd_data = {`DATA_WIDTH{1'b0}};
   //i = 0;


   repeat (10000)@(posedge exec_rd_req)begin

	repeat(1)@(posedge clk);

		if(exec_rd_addr === 12'o1010)begin
			ran1 = 12'o0000;
		end

		else if(exec_rd_addr === 12'o1717)begin
			ran1 = 12'o7777;
		end
	
		else begin
			ran1 = $urandom_range(4096);
		end
		$display("@%2dns exec_rd_data = %d",$time,ran1);
		int_exec_rd_data = ran1;

   end
   
end

   assign exec_rd_data = int_exec_rd_data;

endmodule // memory_pdp
