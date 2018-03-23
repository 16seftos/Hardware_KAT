`timescale 1ns / 1ps

////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer:
//
// Create Date:   14:31:51 03/17/2018
// Design Name:   secjmp
// Module Name:   /home/seaghan/Desktop/SecKat/verilog_tests/secjmp/xilinx/secjmp/secjmp_tb.v
// Project Name:  secjmp
// Target Device:  
// Tool versions:  
// Description: 
//
// Verilog Test Fixture created by ISE for module: secjmp
//
// Dependencies:
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
////////////////////////////////////////////////////////////////////////////////

module secjmp_tb;
  reg [63:0] exp_o;

  // Inputs
  reg [63:0] i;

  // Outputs
  wire [63:0] o;

  // Instantiate the Unit Under Test (UUT)
  secjmp uut (
    .i(i), 
    .o(o)
  );

  initial begin
    // Initialize Inputs
    i = 0;

    // Wait 100 ns for global reset to finish
    #10;
        
    // Add stimulus here
    $monitor("\nTesting");#1;
    // Note:  Secure address is nonzero (?)
    // ignore the MSW 63:32
    $monitor("\nTestintg non-jump instruction");
      i     <= 32'h20210001;
      exp_o <= 32'h20210001;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
      end
    #10;
    
    $monitor("\nTesting secure jump (should noop)");
      i     <= 32'h08000000;
      exp_o <= 32'h00000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
      end
    #10;
    
    $monitor("\nTestintg insecure jump (should pass through)");
      i     <= 32'h0800FACE;
      exp_o <= 32'h0800FACE;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
      end
    #10;
	 
	 $monitor("\nTesting secure jump and link (should noop)");
      i     <= 32'h0C000000;
      exp_o <= 32'h00000000;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
      end
    #10;
    
    $monitor("\nTestintg insecure jump and link (should pass through)");
      i     <= 32'h0C00FACE;
      exp_o <= 32'h0C00FACE;
      #1;
      if(exp_o == o) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
      end
    #10;
    
    $monitor("\nDone testing, exiting\n");#1;
    $finish();
    
  end
      
endmodule

