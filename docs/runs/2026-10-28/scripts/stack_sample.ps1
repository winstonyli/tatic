# stack_sample.ps1 -ProcId <pid> -ThreadId <tid> [-Samples 40] [-StackBytes 262144] -Out <file>: a debugger-free look at
# where a live thread of one of our own processes spins (no admin, no attach). Each sample suspends the thread, reads
# its rip and rsp, and every 8-byte stack word from rsp up that points into the main module, then resumes it. Writes one
# line per sample to <file>: `rip <rva>` then `stack <rva> <rva> ...` (innermost first), RVAs in hex from the module's
# load address. The stack words include stale return addresses, so read frames that recur in every sample. Name them
# with llvm-symbolizer against the exe's PDB at image base 0x140000000 (stack_names.sh). Written 2026-10-28 for the
# mines' hang at low join budgets (docs/tier-cycle.md, "A join budget for the mines alone").
param([Parameter(Mandatory)][int]$ProcId, [Parameter(Mandatory)][int]$ThreadId, [int]$Samples = 40, [int]$StackBytes = 262144,
      [Parameter(Mandatory)][string]$Out)
$ErrorActionPreference = 'Stop'
Add-Type -TypeDefinition @'
using System; using System.Runtime.InteropServices;
public static class SS {
    [DllImport("kernel32.dll", SetLastError=true)] public static extern IntPtr OpenThread(int access, bool inherit, int tid);
    [DllImport("kernel32.dll", SetLastError=true)] public static extern IntPtr OpenProcess(int access, bool inherit, int pid);
    [DllImport("kernel32.dll", SetLastError=true)] public static extern int SuspendThread(IntPtr h);
    [DllImport("kernel32.dll", SetLastError=true)] public static extern int ResumeThread(IntPtr h);
    [DllImport("kernel32.dll", SetLastError=true)] public static extern bool GetThreadContext(IntPtr h, IntPtr ctx);
    [DllImport("kernel32.dll", SetLastError=true)] public static extern bool ReadProcessMemory(IntPtr p, IntPtr addr, byte[] buf, IntPtr n, out IntPtr read);
    [DllImport("kernel32.dll")] public static extern bool CloseHandle(IntPtr h);
}
'@
$proc = Get-Process -Id $ProcId
$base = [int64]$proc.MainModule.BaseAddress; $size = [int64]$proc.MainModule.ModuleMemorySize
$hp = [SS]::OpenProcess(0x0410, $false, $ProcId)                 # PROCESS_QUERY_INFORMATION | PROCESS_VM_READ
$ht = [SS]::OpenThread(0x0002 -bor 0x0008, $false, $ThreadId)     # THREAD_SUSPEND_RESUME | THREAD_GET_CONTEXT
if ($hp -eq [IntPtr]::Zero -or $ht -eq [IntPtr]::Zero) { throw "open failed: $([Runtime.InteropServices.Marshal]::GetLastWin32Error())" }
# an x64 CONTEXT (1232 bytes), 16-byte aligned; ContextFlags at 0x30, Rsp at 0x98, Rip at 0xF8
$raw = [Runtime.InteropServices.Marshal]::AllocHGlobal(1232 + 16)
$ctx = [IntPtr](([int64]$raw + 15) -band -16)
$buf = New-Object byte[] $StackBytes
$lines = New-Object System.Collections.Generic.List[string]
try {
    for ($i = 0; $i -lt $Samples; $i++) {
        for ($k = 0; $k -lt 1232; $k += 8) { [Runtime.InteropServices.Marshal]::WriteInt64($ctx, $k, 0) }
        [Runtime.InteropServices.Marshal]::WriteInt32($ctx, 0x30, 0x100003)   # CONTEXT_AMD64 | CONTROL | INTEGER
        if ([SS]::SuspendThread($ht) -lt 0) { throw "suspend failed" }
        try {
            if (-not [SS]::GetThreadContext($ht, $ctx)) { throw "context failed: $([Runtime.InteropServices.Marshal]::GetLastWin32Error())" }
            $rip = [Runtime.InteropServices.Marshal]::ReadInt64($ctx, 0xF8); $rsp = [Runtime.InteropServices.Marshal]::ReadInt64($ctx, 0x98)
            $read = [IntPtr]::Zero
            $null = [SS]::ReadProcessMemory($hp, [IntPtr]$rsp, $buf, [IntPtr]$StackBytes, [ref]$read)
        } finally { $null = [SS]::ResumeThread($ht) }
        $words = for ($o = 0; $o + 8 -le [int64]$read; $o += 8) { $w = [BitConverter]::ToInt64($buf, $o); if ($w -ge $base -and $w -lt $base + $size) { '{0:x}' -f ($w - $base) } }
        $lines.Add(('rip {0:x}' -f ($rip - $base))); $lines.Add('stack ' + ($words -join ' '))
        [Threading.Thread]::Sleep(50)   # spacing between samples of a thread that never blocks, not a wait on a condition
    }
} finally { [Runtime.InteropServices.Marshal]::FreeHGlobal($raw); $null = [SS]::CloseHandle($ht); $null = [SS]::CloseHandle($hp) }
[IO.File]::WriteAllLines($Out, $lines)
"$Samples samples of thread $ThreadId in $($proc.ProcessName) ($ProcId) to $Out"
