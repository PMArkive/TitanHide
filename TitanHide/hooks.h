#ifndef _HOOKS_H
#define _HOOKS_H

#include "_global.h"

class Hooks
{
public:
    static int Initialize();
    static void Deinitialize();
    static bool RegisterVirtualThreadHide(PETHREAD Thread);
    static bool IsThreadHideVirtualizationAvailable();
    static void RestoreVirtualThreadHides(ULONG ProcessId, bool AllProcesses);
};

#endif