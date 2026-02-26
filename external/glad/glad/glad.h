// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// glad.h — Minimal OpenGL 3.3 core profile STUB header.
// Placeholder for the actual generated glad loader (https://glad.dav1d.de/).
// Provides enough declarations for the shader rendering pipeline to compile.

#ifndef GLAD_GLAD_H
#define GLAD_GLAD_H

#ifdef __cplusplus
extern "C" {
#endif

// ---------------------------------------------------------------------------
// GL version macro
// ---------------------------------------------------------------------------
#define GLAD_GL_VERSION_3_3 1

// ---------------------------------------------------------------------------
// GL type definitions
// ---------------------------------------------------------------------------
typedef unsigned int   GLuint;
typedef int            GLint;
typedef unsigned int   GLenum;
typedef int            GLsizei;
typedef unsigned char  GLboolean;
typedef char           GLchar;
typedef float          GLfloat;
typedef void           GLvoid;
typedef unsigned int   GLbitfield;
typedef long long      GLsizeiptr;
typedef long long      GLintptr;

// ---------------------------------------------------------------------------
// GL constants
// ---------------------------------------------------------------------------
#define GL_VERTEX_SHADER        0x8B31
#define GL_FRAGMENT_SHADER      0x8B30
#define GL_COMPILE_STATUS       0x8B81
#define GL_LINK_STATUS          0x8B82
#define GL_TRUE                 1
#define GL_FALSE                0
#define GL_FLOAT                0x1406
#define GL_TRIANGLES            0x0004
#define GL_ARRAY_BUFFER         0x8892
#define GL_STATIC_DRAW          0x88E4
#define GL_FRAMEBUFFER          0x8D40
#define GL_COLOR_ATTACHMENT0    0x8CE0
#define GL_FRAMEBUFFER_COMPLETE 0x8CD5
#define GL_TEXTURE_2D           0x0DE1
#define GL_RGB                  0x1907
#define GL_UNSIGNED_BYTE        0x1401
#define GL_TEXTURE_MIN_FILTER   0x2801
#define GL_TEXTURE_MAG_FILTER   0x2800
#define GL_LINEAR               0x2601
#define GL_NEAREST              0x2600
#define GL_COLOR_BUFFER_BIT     0x00004000
#define GL_TEXTURE0             0x84C0
#define GL_INFO_LOG_LENGTH      0x8B84

// ---------------------------------------------------------------------------
// glad loader
// ---------------------------------------------------------------------------
extern int gladLoadGLLoader(void* (*load)(const char *name));

// ---------------------------------------------------------------------------
// GL function pointer declarations
// ---------------------------------------------------------------------------
extern GLuint  (*glCreateShader)(GLenum type);
extern void    (*glShaderSource)(GLuint shader, GLsizei count,
                                 const GLchar *const* string,
                                 const GLint *length);
extern void    (*glCompileShader)(GLuint shader);
extern void    (*glGetShaderiv)(GLuint shader, GLenum pname, GLint *params);
extern void    (*glGetShaderInfoLog)(GLuint shader, GLsizei bufSize,
                                     GLsizei *length, GLchar *infoLog);
extern GLuint  (*glCreateProgram)(void);
extern void    (*glAttachShader)(GLuint program, GLuint shader);
extern void    (*glLinkProgram)(GLuint program);
extern void    (*glGetProgramiv)(GLuint program, GLenum pname, GLint *params);
extern void    (*glGetProgramInfoLog)(GLuint program, GLsizei bufSize,
                                      GLsizei *length, GLchar *infoLog);
extern void    (*glDeleteShader)(GLuint shader);
extern void    (*glDeleteProgram)(GLuint program);
extern void    (*glUseProgram)(GLuint program);

extern void    (*glGenVertexArrays)(GLsizei n, GLuint *arrays);
extern void    (*glBindVertexArray)(GLuint array);
extern void    (*glDeleteVertexArrays)(GLsizei n, const GLuint *arrays);

extern void    (*glGenBuffers)(GLsizei n, GLuint *buffers);
extern void    (*glBindBuffer)(GLenum target, GLuint buffer);
extern void    (*glBufferData)(GLenum target, GLsizeiptr size,
                               const void *data, GLenum usage);
extern void    (*glDeleteBuffers)(GLsizei n, const GLuint *buffers);

extern void    (*glVertexAttribPointer)(GLuint index, GLint size, GLenum type,
                                        GLboolean normalized, GLsizei stride,
                                        const void *pointer);
extern void    (*glEnableVertexAttribArray)(GLuint index);

extern void    (*glDrawArrays)(GLenum mode, GLint first, GLsizei count);

extern void    (*glGenFramebuffers)(GLsizei n, GLuint *framebuffers);
extern void    (*glBindFramebuffer)(GLenum target, GLuint framebuffer);
extern void    (*glFramebufferTexture2D)(GLenum target, GLenum attachment,
                                         GLenum textarget, GLuint texture,
                                         GLint level);
extern void    (*glDeleteFramebuffers)(GLsizei n,
                                       const GLuint *framebuffers);

extern void    (*glGenTextures)(GLsizei n, GLuint *textures);
extern void    (*glBindTexture)(GLenum target, GLuint texture);
extern void    (*glTexImage2D)(GLenum target, GLint level,
                               GLint internalformat, GLsizei width,
                               GLsizei height, GLint border, GLenum format,
                               GLenum type, const void *pixels);
extern void    (*glTexParameteri)(GLenum target, GLenum pname, GLint param);
extern void    (*glDeleteTextures)(GLsizei n, const GLuint *textures);

extern GLint   (*glGetUniformLocation)(GLuint program, const GLchar *name);
extern void    (*glUniform1i)(GLint location, GLint v0);
extern void    (*glUniform1f)(GLint location, GLfloat v0);
extern void    (*glUniform2f)(GLint location, GLfloat v0, GLfloat v1);

extern void    (*glViewport)(GLint x, GLint y, GLsizei width, GLsizei height);
extern void    (*glClear)(GLbitfield mask);
extern void    (*glClearColor)(GLfloat red, GLfloat green, GLfloat blue,
                               GLfloat alpha);

extern void    (*glActiveTexture)(GLenum texture);
extern GLenum  (*glCheckFramebufferStatus)(GLenum target);

#ifdef __cplusplus
} // extern "C"
#endif

#endif // GLAD_GLAD_H
