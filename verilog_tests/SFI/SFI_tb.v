`timescale 1ns / 1ps

////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer:
//
// Create Date:   18:22:49 03/16/2018
// Design Name:   SFI
// Module Name:   /home/seaghan/Desktop/SecKat/verilog_tests/SFI/xilinx/SFI/SFI_tb.v
// Project Name:  SFI
// Target Device:  
// Tool versions:  
// Description: 
//
// Verilog Test Fixture created by ISE for module: SFI
//
// Dependencies:
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
////////////////////////////////////////////////////////////////////////////////

module SFI_tb;

  // Inputs
  reg [63:0] ri;

  // Outputs
  wire [63:0] ro;

  // Instantiate the Unit Under Test (UUT)
  SFI uut (
    .ri(ri), 
    .ro(ro)
  );

  // Expected output register
  reg [63:0] exp_ro;
  reg all_pass;

  initial begin
    // Initialize Inputs
    ri = 0;
    exp_ro = 0;
	 all_pass = 1;

    // Wait 10 ns for global reset to finish
    #10;
        
    // Add stimulus here
    $monitor("\nTesting");#1;
    $monitor("\nTestintg bad eff addr:");
      ri     <= 64'hBAD0ADD012345678;
      exp_ro <= 64'h0000000000000000;
		// Should this pass the last 32b?
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
	     all_pass = 0;
      end
    #10;
    
    $monitor("\nTestintg good eff addr:");
      ri     <= 64'hA219987200000000;
      exp_ro <= 64'hA219987200000000;
      #1;
      if(exp_ro == ro) begin
        $monitor("\tPassed");
      end else begin
        $monitor("\tFailed");
	     all_pass = 0;
      end
    #10;
    
    $monitor("\nDone testing, exiting\n");#1;
	 if(all_pass == 1) begin
	   $monitor("All Pass");#1;
	 end else begin
		$monitor("Not all pass");#1;
	 end
    $finish();
      
  end
      
endmodule

