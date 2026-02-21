#pragma once
// Forwarding header: legends -> aibox unification
#ifdef _MSC_VER
#pragma warning(push)
#pragma warning(disable: 4201)  // nonstandard extension: nameless struct/union
#endif
#include <aibox/cpu_context.h>
#ifdef _MSC_VER
#pragma warning(pop)
#endif
namespace legends { using namespace aibox; }
