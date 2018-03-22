`timescale 1ns / 1ps

////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer:
//
// Create Date:   20:08:10 03/21/2018
// Design Name:   taint
// Module Name:   /home/seaghan/Desktop/SecKat/verilog_tests/taint/xilinx/taint/taint_tb.v
// Project Name:  taint
// Target Device:  
// Tool versions:  
// Description: 
//
// Verilog Test Fixture created by ISE for module: taint
//
// Dependencies:
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
////////////////////////////////////////////////////////////////////////////////

module taint_tb;

  // Inputs
  reg [63:0] i;

  // Outputs
  wire [63:0] o;
   
  //Experemental values
  reg [63:0] exp_o;
  reg all_pass;

  // Instantiate the Unit Under Test (UUT)
  taint uut (
    .i(i), 
    .o(o)
  );

  initial begin
    // Initialize Inputs
    i = 0;
    exp_o = 0;
    all_pass = 1;

    // Wait 10 ns for global reset to finish
    #10;
        
    // Add stimulus here
    $monitor("\nTesting");#1;
    $monitor("\nTestintg no taint:");
      //these are from other programs I wrote, or random inputs
      i     <= 64'h7000000070000000;
      exp_o <= 64'h7000000070000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
      i     <= 64'h70042331700FACE0;
      exp_o <= 64'h70042331700FACE0;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
      i     <= 64'h700000000CAEF120;
      exp_o <= 64'h700000000CAEF120;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
      i     <= 64'h0000000000000000;
      exp_o <= 64'h0000000000000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
    #10;
    
    //Left taint
    $monitor("\nTestintg left taint:");
      //these are from other programs I wrote, or random inputs
      i     <= 64'hE000000070000000;
      exp_o <= 64'hE0000000F0000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
      i     <= 64'h80042331700FACE0;
      exp_o <= 64'h80042331F00FACE0;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
      i     <= 64'hF00000000CAEF120;
      exp_o <= 64'hF00000008CAEF120;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
      i     <= 64'h8000000000000000;
      exp_o <= 64'h8000000080000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
    #10;
    
    //Right taint
    $monitor("\nTestintg right taint:");
      //these are from other programs I wrote, or random inputs
      i     <= 64'h70000000FACE0000;
      exp_o <= 64'hF0000000FACE0000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
      i     <= 64'h70042331F00FACE0;
      exp_o <= 64'hF0042331F00FACE0;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
      i     <= 64'h700000008CAEF120;
      exp_o <= 64'hF00000008CAEF120;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
      i     <= 64'h0000000080000000;
      exp_o <= 64'h8000000080000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
    #10;
    
    //Both taint
    $monitor("\nTestintg both taint:");
      //these are from other programs I wrote, or random inputs
      i     <= 64'hF0000000FACE0000;
      exp_o <= 64'hF0000000FACE0000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
      i     <= 64'hF0042331F00FACE0;
      exp_o <= 64'hF0042331F00FACE0;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
      i     <= 64'hF00000008CAEF120;
      exp_o <= 64'hF00000008CAEF120;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
      i     <= 64'h8000000080000000;
      exp_o <= 64'h8000000080000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
       all_pass = 0;
      end
      #1;
    #10;
   
  //FINISHED TESTING
    $monitor("\nDone testing, exiting\n");#1;
  if(all_pass == 1) begin
    $monitor("All Pass");#1;
  end else begin
    $monitor("Not all pass");#1;
  end
  $finish();
      
  end
      
endmodule

