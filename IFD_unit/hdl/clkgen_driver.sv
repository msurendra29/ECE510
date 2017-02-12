// =======================================================================
//   Department of Electrical and Computer Engineering
//   Portland State University
//
//   Course name:  ECE 510 - Pre-Silicon Validation
//   Term & Year:  Spring 2016
//   Instructor :  Tareque Ahmad
//
//   Project:      Hardware implementation of PDP8 
//                 Instruction Set Architecture (ISA) level simulator
//
//   Filename:     clkgen_driver.sv
//   Description:  Independent clock and reset genrator
//                 Clock: 50% duty cycle clock with parameterized time period
//                 Reset: Active low. Asynchronous with parameterized initial
//                        active low period
//
//   Created by:   Surendra Maddula
//   Date:         May 23, 2016
//
//   Copyright:    Surendra Maddula, Bharath Reddy Godi
// =======================================================================

`timescale 1ns/1ps

// Import the package
import pdp8_pkg::*;

// Define module
module clkgen_driver
  (
   output clk,
   output reset_n
   );

   // Define parameters
   parameter CLOCK_PERIOD = 10;
   parameter RESET_DURATION = 500;
   parameter RUN_TIME = 5000000;
   parameter REST_TIME = 245700;

   // Define internal registers
   reg int_clk;
   reg int_reset_n;

   // Generate fixed frequency internal clock
   initial begin
      int_clk = 0;
      forever #(CLOCK_PERIOD/2) int_clk = ~int_clk;
   end

   // Generate one-time internal reset signal
   initial begin
      int_reset_n = 0;
      # RESET_DURATION int_reset_n = 1;
      # RUN_TIME
      $finish;
   end

   always begin
      # REST_TIME int_reset_n = 0;
	$display("@%2dns Reset",$time);
      # (CLOCK_PERIOD *10) int_reset_n = 1;
      //# (CLOCK_PERIOD *100) int_reset_n = 0;
      //# (CLOCK_PERIOD *2) int_reset_n = 1;
   end

   // Continuous assignment to output
   assign clk     = int_clk;
   assign reset_n = int_reset_n;

endmodule

